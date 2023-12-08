module QName where -- Qualified names; module + iname as a machine integer
newtype QName = QName Int deriving (Show , Eq , Ord)
newtype VQBindIndex = VQBindIndex QName deriving Eq

-- the lower `moduleBits` of are reserved as module identifiers.
-- The idea is to always deal with native Ints, particularly for use as IntMap keys

-- Note. Ints are signed, div truncates, so this is skewed by 2 bits, and thus there are 4x more bindnames than module names
moduleBits    :: Int = floor (logBase 2 (fromIntegral (maxBound ∷ Int))) `div` 2
maxModuleName :: Int = modName (QName (complement 0))
maxIName      :: Int = unQName (QName (complement 0))
fieldBit = moduleBits + 1
labelBit = moduleBits + 2

qName2Key (QName q) = q -- somewhat annoying but Intmap insists
mkQName m i       = QName ((i `shiftL` moduleBits) .|. m)
unQName (QName q) = q `shiftR` moduleBits
modName (QName q) = q .&. complement (complement 0 `shiftL` moduleBits)

showRawQName q = show (modName q) <> "." <> show (unQName q)
