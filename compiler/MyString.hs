-- unfoldr with additional option to unfold bytestring and ints for convenience and perf
-- Data.ByteString.unfoldr is very inefficient due to use of concat and multiple <>
module MyString where -- (NextChunk(..) , unfoldrChunks) where
import Foreign.ForeignPtr
import Foreign.Storable
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BS
import qualified Data.ByteString.Internal as BSI
import System.IO.Unsafe
import Foreign.Marshal.Alloc
import Foreign.Marshal.Utils
import Foreign.Ptr
-- import qualified Data.Vector as V

import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Generic.Mutable as VGM

constructN :: forall v a. VG.Vector v a => Int -> (v a -> a) -> v a
{-# INLINE constructN #-}
constructN n f = let
  fill :: forall s. Int -> v a -> ST s (v a)
  fill i v = if i < n then let x = f (VG.unsafeTake i v) in VG.elemseq v x $ VG.unsafeThaw v >>= \v' ->
    VGM.unsafeWrite v' i x *> VG.unsafeFreeze v' >>= fill (i + 1)
    else return v
  in runST (VGM.new n >>= VG.unsafeFreeze >>= fill 0)

constructNSeed :: forall v a seed. (VG.Vector v a) => Int -> (v a -> seed -> (a , seed)) -> seed -> (seed , v a)
constructNSeed n f inSeed = let
  fill :: forall s. Int -> (seed , v a) -> ST s (seed , v a)
  fill i (inSeed , v) = if
    | i < n -> let (x , outSeed) = f (VG.unsafeTake i v) inSeed in VG.elemseq v x $ VG.unsafeThaw v >>= \v' ->
      VGM.unsafeWrite v' i x *> VG.unsafeFreeze v' >>= \nextV -> fill (i + 1) (outSeed , nextV)
    | i >= n -> pure (inSeed , v)
  in runST (VGM.new n >>= VG.unsafeFreeze >>= \startV -> fill 0 (inSeed , startV))

data NextChunk seed
 = NEnd seed
 | NSkip seed
 | NChar Char seed
 | NChunks [Either ByteString seed]
 | NBStr ByteString
 | NStr  ByteString seed
 | NEnclose ByteString seed ByteString
 | NEndStr  seed ByteString

{- INLINE unfoldrChunks -}
unfoldrChunks :: (seed -> NextChunk seed) -> seed -> (seed , BS.ByteString)
unfoldrChunks = unfoldrChunksN 256

{- INLINE unfoldrChunksN -}
-- TODO track buflen properly everywhere
unfoldrChunksN :: Int -> (seed -> NextChunk seed) -> seed -> (seed , BS.ByteString)
unfoldrChunksN startLen next startSeed = let
--loop :: Ptr a -> Int -> Int -> seed -> IO (Ptr a , Int , seed)
  loop ptr bufLen i seed = loopCase ptr bufLen i seed (next seed)
  appendByteString bs ptr bufLen i = BSI.toForeignPtr0 bs & \(fptr , len) -> if i + len < bufLen
    then (bufLen , ptr , i + len) <$ withForeignPtr fptr (\p -> copyBytes (plusPtr ptr i) p len)
    else let newLen = bufLen * 2 in reallocBytes ptr newLen >>= \newPtr -> appendByteString bs newPtr newLen i
  loopCase ptr bufLen i seed = \case
    NEnd endSeed -> pure (ptr , i , endSeed)
    NSkip reseed -> loop ptr bufLen i reseed
    NChar c d | i < bufLen -> pokeByteOff ptr i c *> loop ptr bufLen (i + 1) d

    NBStr  s  -> appendByteString s ptr bufLen i <&> \(bufLen , ptr , i) -> (ptr , i , seed)
    NStr  s d -> appendByteString s ptr bufLen i >>= \(bufLen , ptr , i) -> loop ptr bufLen i d
    NEnclose a s b -> appendByteString a ptr bufLen i >>= \(bufLen2 , ptr2 , i2) ->
      loopCase ptr2 bufLen2 i2 seed (NEndStr s b)
    NEndStr d s -> loop ptr bufLen i d >>= \(ptr' , i' , seed') ->
      appendByteString s ptr' bufLen i' <&> \(bufLen , ptr , i) -> (ptr , i , seed')

--  NList (s :| ss) -> let foldFn (ptr' , i' , _s') seed = loop ptr' bufLen i' seed
--    in loop ptr i bufLen s >>= \start -> foldM foldFn start ss

    NChunks [] -> error ""
    NChunks cs -> let
      foldFn (ptr , i , prevSeed) = \case
        Left str   -> appendByteString str ptr bufLen i <&> \(bufLen , ptr , i) -> (ptr , i , prevSeed)
        Right seed -> loop ptr bufLen i seed -- discard prevSeed
      in foldM foldFn (ptr , i , seed) cs

    nxt -> let newLen = bufLen * 2 in reallocBytes ptr newLen >>= \newPtr -> loopCase newPtr newLen i seed nxt
  in unsafeDupablePerformIO $ mallocBytes startLen >>= \startPtr ->
    loop startPtr startLen 0 startSeed >>= \(ptr , i , seed) ->
      (seed , ) <$> BS.unsafePackCStringFinalizer (castPtr ptr) i (free ptr)

testF 0 = NChar 'x' 1
testF 1 = NStr "Hello" 2
testF 2 = NChar '3' 3
testF 3 = NStr "indeed" 4
testF 4 = NEnclose "( " 5 " )"
testF 5 = NEndStr 6 "xdd"
testF 6 = NStr "6" 7
testF n = NEnd n

test = unfoldrChunks testF (0 :: Int)
