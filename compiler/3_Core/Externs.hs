module Externs (Externs(..) , readPrimExtern , readParseExtern , typeOfLit) where
import Builtins ( primBinds , typeOfLit )
import CoreSyn
import ShowCore()
import qualified Data.Vector as V

-- how to substitute P.VExtern during mixfix resolution
newtype Externs = Externs {
   extNames      :: V.Vector ExternVar
-- , importLabels  :: V.Vector QName
} deriving Show

--readLabel {-, readField-} :: Externs -> IName -> QName
--readLabel exts l = if l < 0 then mkQName 0 (-1 - l) else exts.importLabels V.! l

readPrimExtern e i = snd (primBinds V.! i) -- snd (extBinds e V.! 0 V.! i)

-- exported functions to resolve ParseSyn.VExterns
--readQParseExtern :: BitSet -> Int -> Externs -> Int -> IName -> CoreSyn.ExternVar
--readQParseExtern openMods thisModIName (exts :: Externs) modNm iNm = if
--  | modNm == thisModIName    -> ForwardRef iNm -- solveScopes can handle this
-- | openMods `testBit` modNm -> Imported $ case snd (exts.extBinds V.! modNm V.! iNm) of
--   e@(Core f t) -> case f of -- inline trivial things
--     Lit{}   -> e
--     Instr{} -> e
--     Var{}   -> e -- var indirection (TODO continue maybe inlining?)
--     _ -> e
--     _ -> Core (Var $ VQBind (mkQName modNm iNm)) t
--  | otherwise -> NotOpened (show modNm {-exts.eModNamesV V.! modNm-}) (fst (exts.extBinds V.! modNm V.! iNm))

readParseExtern :: _ -> ModIName -> Externs -> IName -> ExternVar
readParseExtern openMods thisModIName exts i = case exts.extNames V.! i of
  Importable modNm iNm -> if modNm == thisModIName then ForwardRef iNm
    else _ -- readQParseExtern openMods thisModIName exts modNm iNm
  x -> x
