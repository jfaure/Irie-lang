{-# Language TemplateHaskell #-}
module Externs (Externs(..) , readPrimExtern , readParseExtern , typeOfLit , LoadedMod(..) , Import(..) , Deps , Dependents , showImportCon , readQName) where
import Builtins ( primBinds , typeOfLit )
import CoreSyn
import ShowCore()
import CoreUtils(bind2Expr)
import qualified Data.Vector as V
import Text.Megaparsec (ParseErrorBundle)
import qualified ParseSyntax as P
import Errors
import Control.Lens

-- how to substitute P.VExtern during mixfix resolution
type Deps = BitSet
type Dependents = BitSet

-- TODO ? should all have a ModIName
data Import
 = ImportName Text
 | NoPath  Text
 | NoParse Text (ParseErrorBundle Text Void)
 | ImportLoop BitSet -- All deps known; but the loop must be handled specially
 | ParseOK ModIName P.Module -- P.Module contains the filepath
 | JudgeOK ModIName JudgedModule
 | NoJudge ModIName Errors
-- | Cached  ModIName FilePath
 | IRoot -- For compiling multiple files on cmdline without a root module

data LoadedMod = LoadedMod
 { _deps :: Deps
 , _dependents :: Dependents
 , _loadedImport :: Import
 }; makeLenses ''LoadedMod

newtype Externs = Externs { extNames :: V.Vector ExternVar } deriving Show

--readLabel {-, readField-} :: Externs -> IName -> QName
--readLabel exts l = if l < 0 then mkQName 0 (-1 - l) else exts.importLabels V.! l

readPrimExtern e i = snd (primBinds V.! i) -- snd (extBinds e V.! 0 V.! i)

readParseExtern :: _ -> ModIName -> Externs -> IName -> ExternVar
readParseExtern openMods thisModIName exts i = case exts.extNames V.! i of
  Importable modNm iNm -> if
    | modNm == thisModIName -> ForwardRef iNm
    | modNm == 0 -> Imported (snd (primBinds V.! iNm))
    | True -> NotOpened (show modNm <> "." <> show iNm) ("")
    -- readQParseExtern openMods thisModIName exts modNm iNm
  x -> x

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

readQName :: V.Vector LoadedMod -> ModIName -> IName -> ExternVar
readQName curMods modNm iNm = case curMods V.! modNm & \(LoadedMod _ _ m) -> m of
  JudgeOK _ jm -> Imported (readJudgedBind jm iNm)
  s -> Importable modNm iNm

readJudgedBind :: JudgedModule -> IName -> Expr
readJudgedBind m iNm = case m.moduleTT of
  Core (LetBlock binds) _ -> snd (binds V.! iNm) & bind2Expr
  _ -> _

showImportCon :: Import -> Text
showImportCon = \case
 ImportName{} -> "ImportName"
 NoPath{} -> "NoPath"
 NoParse{} -> "NoParse"
 ImportLoop{} -> "ImportLoop"
 ParseOK{} -> "ParseOK"
 JudgeOK{} -> "JudgeOK"
