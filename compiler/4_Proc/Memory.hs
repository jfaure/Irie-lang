module Memory where
import SSA
import qualified CoreSyn as TT
import qualified BitSetMap as BSM
import qualified Data.Vector as V

data FieldTags = FTLarge Word64 | FTSmall Word64
newtype Tag = Tag Int -- how many bits needed

-- mapping of FLabels to [0..]
normaliseLabel ∷ TT.ILabel → BSM.BitSetMap a → Int
normaliseLabel l context = 0

-- [(Int , Either a b)] ⇒ [Int] , ([EitherTags] , [Left a] , [Right b])
-- tree.flowery.tree.tree
-- wraps vs joins
data SSAMemOps e
 = MJoin (Type , e) (Type , e)  -- make larger record
 | MSubRecord Type e FieldTags  -- subtype a record (drop fields)
 | MIndex ROS Int               -- index into a record (+ sumtype tag)
 | MModify Type e Int e         -- update field to different size

 | MEmbedSumtype                -- inc number of alts
 | MTrimSumtype                 -- case-out some alts

 | MCons        [e]             -- merge args
 | MGetRetMem                   -- Sz → Ptr

serialise   ∷ V (ROSField Expr) → Expr
serialise   ros = _
unserialise ∷ Expr → V (ROSField Expr)
unserialise mem = _

memOp2SSA ∷ SSAMemOps e → SSA.CGEnv s Expr
memOp2SSA = \case
  MIndex r i → case sumOffset (r V.! i) of
    Just sumOff → _
--  _field      → field.fieldOffset + popCount (r.fieldTags .&. (1 `shiftL` i)) -- use polyargs to index correctly
  MSubRecord ty r drops → _ -- fieldTags r .&. not drops ; bitTags
     
  MJoin r1 r2 →      _ -- write a new record , sort fields
  MModify ty r i v → _ -- if field becomes larger?

  -- examine bittag then MIndex / cast
  MTrimSumtype  → _ -- reduce size of bittags
  MEmbedSumtype → _ -- inc size of bittags

  -- spawn retptrs to write the args to (check pre-dropped fields before calling a fn)
  -- wrap rec arg(s) or rec call?
  MCons args → case (getWrapRecHeader <|> getRecHeader args) of
    Just rc → _ -- find list for run & add to run-length encoding
    _norec  → _ -- return struct in regs

  MGetRetMem → _ -- either index into fn|cons RetPtr or spawn tmp retMem

getWrapRecHeader = Nothing
getRecHeader args = Nothing

-- Lambda-lifting ⇒ make small normal form of fn compositions, by lambda encoding + lifting + sharing
-- comp n f x = if n == 0 then f x else comp (n - 1) (\k → f (f k)) x
-- comp 1 f x = f (f x)
-- comp 2 f x = f (f (f x))
-- eg. True = \t f ⇒ t ; False = \t f ⇒ f
-- not = \b ⇒ b (\t f ⇒ f) (\t f ⇒ t)
--     = \b t f ⇒ (b f t) -- share lambdas
-- (\b ⇒ not (not b)) = \x t f ⇒ x t f
--
-- proof.
-- not (not x)
-- (\b t f ⇒ b f t) ((\b t f ⇒ b f t) x)
-- (\b t f ⇒ b f t) (\t f ⇒ x f t)
-- \t f ⇒ (\t f ⇒ x f t) f t
-- \t f ⇒ x t f
--
-- Fusion using non-statically known number of applications
-- (Inc x) = let
--   case_e = λe λo λi e
--   case_o = λx λe λo λi (i x)
--   case_i = λx λe λo λi (o (Inc x))
--   in x case_e case_o case_i
-- (Inc x) = λe λo λi
--   case_e = e
--   case_o = λx (i x)
--   case_i = λx (o (Inc x))
--   in x case_e case_o case_i
-- Inc = λg λe λo λi ⇒ g e (\x ⇒ i x) (\x ⇒ o (Inc x))
