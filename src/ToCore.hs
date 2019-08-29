-- convert parse tree to core

-- * names become integers (Human names and other info are in a Vector)
-- * the context must make it clear if something is a type or expr
--   so we never confuse the type/val namespaces. basically:
--   CoreExpr.TypeExpr increases the universe,
--   Type.TyExpr       reduces   the universe
-- * (resolve infix apps (including precedence)) n. do this in seperate pass
-- * desugar PExpr to CoreExpr

{-# LANGUAGE LambdaCase #-}
module ToCore
where

import CoreSyn
import qualified ParseSyntax as P

import qualified Data.Vector as V
import qualified Data.Map as M
import qualified LLVM.AST
import qualified LLVM.AST.Constant as C
import qualified Data.Text as T

import Debug.Trace

-- conversion state is necessary when converting variables to integers
data ConvState = ConvState {
   nameCount :: Name
 , nameMap   :: M.Map HName Entity -- recall entity = (Maybe Name); Type; Universe
}

convTy :: P.Type -> Type
convTy (P.TyLlvm l) = TyMono (MonoTyLlvm l)
convTy (P.TyForall (P.ForallAnd f)) = TyPoly $ ForallAnd $ map convTy f
convTy (P.TyForall (P.ForallOr f)) = TyPoly $ ForallOr $ map convTy f
convTy (P.TyForall (P.ForallAny)) = TyPoly $ ForallAny
convTy (P.TyName n) = _ -- TyRef f
convTy (P.TyArrow tys) = TyArrow $ map convTy tys
convTy (P.TyExpr e) = _ -- TyExpr $ expr2Core e
convTy (P.TyTyped a b) = _
convTy (P.TyUnknown) = TyUnknown

pName2txt (P.UnQual (P.Ident s)) = T.pack s

parseTree2Core :: P.Module -> CoreModule
parseTree2Core parsedDecls = CoreModule V.empty V.empty M.empty --dataDecls topExprs defaults
  where
  decls = V.fromList parsedDecls

  -- data declarations -> we need a type and corresponding list of constructors
  -- these may return a type that subsumes the data's type (GADTS)
  datas = V.filter isData decls :: V.Vector P.Decl
  hTypeNames = getDataHName <$> datas
    where getDataHName (P.TypeAlias nm _) = nm
          getDataHName (P.DataDecl nm _ _) = nm
  -- this function allows us to convert forward type references to their int name
  lookupTyHName hNm = case V.findIndex (==hNm) hTypeNames of { Just n -> n ; _ -> error "name lookup fail" }

  dataEntities = V.imap doData datas
  doData :: int -> P.Decl -> (Entity, ExprMap)
  doData acc (P.TypeAlias pName ty) = (entity,consList) : acc
    where entity = (Entity (Just hNm) (convTy ty) uniType)
  	  hNm = (\(P.Ident h) -> h) $ pName
          consList = []
  doData acc (P.DataDecl hNm kind qCons) = (entity, consList) : acc
    where entity = (Entity (Just hNm) dataTy uniType)
          --dataTy = convTy ty
          dataTy = TyUnknown
          consList = getCon <$> qCons
          getCon :: Type -> P.ConDecl -> (Entity, CoreExpr)
          getCon dataTy (P.ConDecl hNm types) = Entity (Just hNm) (TyArrow (types ++ dataTy))
          getCon dataTy (P.InfixConDecl tyA hNm tyB) = _
          getCon dataTy (P.GadtDecl hNm kind tyVars fields) = _

  defaults = M.empty -- map doDefault (filter isDefault decls)

  -- we have already generated the constructors, so they have priority when naming entities
  topBinds = V.fromList $ V.filter isFunBind (V.fromList decls) :: V.Vector P.Decl
  topSigs  = filter isSig decls
  lookupSig hNm = V.findIndex (elem hNm) topSigs
  -- get all hnames (so we can handle forward references)
  hNameMap = (extractHNames topBinds) :: V.Vector HName
    where extractHNames ((P.FunBind matches) : rem) = (match2Hnm<$>matches) : extractHNames rem
          extractHNames (_:rem) = extractHNames rem
          extractHNames [] = []
          match2Hnm (P.Match nm pats rhs) = nm
          match2Hnm (P.InfixMatch pat nm pats rhs) = nm
  lookupHName :: T.Text -> Int
  lookupHName hNm = V.findIndex (==hNm) hNameMap

  getFnHName :: [P.Match] -> HName
  getFnHName m = case head m of
    P.Match hnm _ _ -> parseName2Text hnm
    P.InfixMatch _ hnm _ _ -> parseName2Text hnm
  topExpr :: V.Vector P.Decl -> ExprMap -- Vector (Entity, CoreExpr)
  topExpr = V.imap doExpr topBinds
  doExpr :: Int -> P.Decl -> (Entity, CoreExpr)
  doExpr nm f@(P.FunBind matches) = (e, cExp)
    where
    hNm = getFnHName f
    e = Entity (Just hNm) ty uniTerm
    ty = lookupSig hNm
    cExp = Case e alts
      where 
            args = []
	    getPrefixMatch (P.InfixMatch p1 nm ps rhs) = P.Match nm (p1:ps) rhs
            getPrefixMatch m = m
            -- Function matches:
            -- many patterns do not result in a variable binding
            alts = match2CaseAlt <$> doInfix <$> matches
            doInfix x@P.Match{} = x
            doInfix (P.InfixMatch pat nm pats rhs) = P.Match nm (pat:pats) rhs
            match2CaseAlt (P.Match hNm pats (P.UnGuardedRhs exp)) =
              let namedVars = V.fromList $ (\(PVar hNm) -> hNm) <$> pat2Core <$> pats -- TODO other patterns
                  rhs = expr2Core [] exp --[namedVars] exp
              in BFn (length pats) rhs

  -- predicates for filtering
  isData, isFunBind, isDefault :: P.Decl -> Bool
  isData = \case { P.TypeAlias{}->True ; P.DataDecl{}->True ; _->False }
  isFunBind = \case { P.FunBind{}->True ; _->False }
  isSig = \case { P.TypeSigDecl{}->True ; _->False }
  isDefault = \case { P.DefaultDecl{}->True ; _->False }

exprLookupName :: [V.Vector HName] -> _ -> Name
exprLookupName (names : rest) hNm = case vFind names of { Nothing -> exprLookupName rest hNm ; Just x -> x }
  where vFind = V.findIndex (==hNm)

parseName2Text = \case { (P.Ident h) -> T.pack h }

expr2Core :: [V.Vector HName] -> P.PExp -> CoreExpr
expr2Core hNames (P.Var (P.UnQual nm)) = Var $ exprLookupName hNames $ parseName2Text nm
expr2Core hNames (P.Con (P.UnQual nm)) = Var $ exprLookupName hNames $ parseName2Text nm
expr2Core hNames (P.Lit l)  = Lit $ literal2Core l
expr2Core hNames (P.Infix nm) = _
expr2Core hNames (P.App f args) = handlePrecedence f args
  where handlePrecedence f args = App (expr2Core hNames f) (expr2Core hNames <$> args)
expr2Core hNames (P.Lambda f args) = _
expr2Core hNames (P.MultiIf alts) = _
expr2Core hNames (P.Case e alts) = _
expr2Core hNames (P.Do stmts) = _ -- exprToCore $ foldr1 desugarStmt stmts
 -- suboptimal.. should use the name number corresponding to ">>" and ">>=" for this.
--  where desugarStmt (P.Qualifier a) (P.Qualifier b) = App (Var (P.Symbol ">>")) [a, b]
expr2Core hNames (P.MDo stmts) = _
expr2Core hNames (P.List f) = _
expr2Core hNames (P.TypeSig e ty) = _
expr2Core hNames (P.AsPat nm pat) = _
expr2Core hNames (P.WildCard) = _
expr2Core hNames (P.TypeExp ty) = _
expr2Core hNames (P.Typed t e) = _

pat2Core :: P.Pat -> Pat
pat2Core (P.PVar n) = _ -- PVar 1
pat2Core (P.PLit l) = PLit $ literal2Core l
--pat2Core (P.PInfixApp p1 n ps) = pat2Core (P.PApp n ((pat2Core p1):(pat2Core ps):[]))
pat2Core (P.PApp qNm ps) = _
pat2Core (P.PTuple p) = PTuple (pat2Core <$> p)
pat2Core (P.PList ps) = _
pat2Core (P.PWildCard) = PWildCard

literal2Core :: P.Literal -> Literal
literal2Core (P.Char c) = _ -- LlvmLit $ LLVM.AST.ConstantOperand $ C.Int 8 $ fromInteger c
--literal2Core (P.String c) = String c
--literal2Core (P.Int c) = Int c
--literal2Core (P.Frac c) = Frac c
