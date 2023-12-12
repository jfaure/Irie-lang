module Caster where
import Prim
import CoreSyn
import PrettyCore
import qualified BitSetMap as BSM
import qualified Data.Vector as V

-- * BasicTypes: No type merges , no tvars
-- ? Type applications , type params / μ params
-- ? Lift&type/inline/specialise lams/paps
-- ? Dups
-- ? only Binds can be functions & must be η-expanded

-- TODO
-- * Parser: pre-lift all case-alts & bruijnAbs (pre-emptive specialisation)
-- * Infer: Add TypeApp to Core (explicit instantiation primitive)
-- * β-env: polyType specialisations , track types & insert casts
-- * Caster: Insert casts after all types inferred , before C emission
--   rm implicit label/prod when 1 alt/field
--   ↓ abs types ↑ type of exprs

-- post-infer casts are forced because eg:
--   eg. either = \case {Left a => a ; Right a => add a 3 }
--    : "Either A Int -> Int ⊔ A"
--   A between [⊥ , Int]; infer can't cast it because depends on tvar bounds.

-- idea: newtype BasicType = THead BasicType -- ie. No meet/joins.
-- Also need BasicType -> Type function so it can participate in inferrence

-- TODO alignment requirements
sizeOfPrim = let
  bitSize n = div n 8
  in \case
  PrimInt n -> bitSize n
  PrimNat n -> bitSize n
  _ -> _

-- size in bytes of a type
sizeOf :: Type -> Int
sizeOf = \case
  TyGround [t] -> case t of
    THPrim p -> sizeOfPrim p
    THTyCon tycon -> case tycon of
      THTuple t -> if null t then 0 else sum (sizeOf <$> t)
  _ -> _

-- pass down typedef for structure types
unTyGround (TyGround [t]) = t
tyToBasicTy :: TyHead -> BasicType
tyToBasicTy = let
  doTy = tyToBasicTy . unTyGround
  in \case
  THPrim p -> BPrim p
  THTyCon tcon -> case tcon of
    THProduct bsm -> BStruct (bsm <&> \(TyGround [t]) -> tyToBasicTy t)
    THTuple   tys -> BStruct (BSM.fromVec $ V.imap (\i (TyGround [t]) -> (qName2Key (mkQName 0 i) , tyToBasicTy t)) tys)
    THSumTy   bsm -> let
      collect :: Int -> (Int , Type) -> Int
      collect (maxSz) (_qNm , ty) = (max maxSz (sizeOf ty))
      maxSz = BSM.foldlWithKey collect 0 bsm
      tagCount = BSM.size bsm -- bits = intLog2 tagCount
      in if
        | maxSz    == 0 -> BEnum tagCount --  (PrimNat bits)
        | tagCount == 1 , [(tag , TyGround [ty])] <- BSM.toList bsm ->
          BSum tagCount (BSM.singleton tag (tyToBasicTy ty)) maxSz
        | True -> BSum tagCount (doTy <$> bsm) maxSz
    THArrow aTs rT -> BArrow (doTy <$> aTs) (doTy rT)
    t -> traceTy (TyGround [THTyCon t]) (error "")
  THBi _ (TyGround [ty]) -> tyToBasicTy ty
  THBound i -> BBound i
--THSet 0 -> BBound i
  t -> traceTy (TyGround [t]) (error $ show t)
