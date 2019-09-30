-- convert parse tree to core

-- * names become integers (Human names and other info are in a Vector)
-- * the context must make it clear if something is a type or expr
--   so we never confuse the type/val namespaces. basically:
--   CoreExpr.TypeExpr increases the universe,
--   Type.TyExpr       reduces   the universe
-- * (resolve infix apps (including precedence)) n. do this in seperate pass
-- * desugar PExpr to CoreExpr

{-# LANGUAGE LambdaCase, ScopedTypeVariables, MultiWayIf #-}
module ToCore
where

import CoreSyn
import qualified ParseSyntax as P

import qualified Data.Vector as V
import qualified Data.Map.Strict as M
import qualified LLVM.AST
import qualified LLVM.AST.Constant as C
import qualified Data.Text as T
import Control.Monad.Trans.State.Strict

import GHC.Exts (groupWith)
import Data.Char (ord)
import Control.Monad (zipWithM)
import Control.Applicative ((<|>))

import Debug.Trace

-- conversion state is necessary when converting variables to integers
type ToCoreEnv a = State ConvState a
data ConvState = ConvState {
   nameCount     :: Name
 , localHNames   :: M.Map HName Name -- bindings
 , localTypeVars :: M.Map HName Name -- flexible type vars
 , localBinds    :: V.Vector Binding
 , toCoreErrors  :: [ToCoreErrors]
}
type ToCoreErrors = String

convTy :: P.Type -> Type
 = \case
  P.TyLlvm l                 -> TyMono (MonoTyLlvm l)
  P.TyForall (P.ForallAnd f) -> TyPoly $ ForallAnd $ map convTy f
  P.TyForall (P.ForallOr f)  -> TyPoly $ ForallOr $ map convTy f
  P.TyForall (P.ForallAny)   -> TyPoly $ ForallAny
  P.TyName n                 -> TyVar $ pName2Text n
  P.TyArrow tys'             ->
    let tys = convTy <$> tys'
        args = init tys
        retTy = last tys
    in TyArrow args retTy
  P.TyExpr e                 -> _ -- TyExpr $ expr2Core e
  P.TyTyped a b              -> _
  P.TyUnknown                -> TyUnknown

pName2Text = \case
  P.Ident h -> T.pack h
  P.Symbol s -> T.pack s
pQName2Text (P.UnQual (P.Ident s)) = T.pack s

parseTree2Core :: P.Module -> CoreModule
parseTree2Core parsedTree' = CoreModule
  { types         = dataEntities
  , topExprs      = topBinds
  , localBindings = localBinds'
  , defaults      = defaults
  }
  where
  parsedTree  = V.fromList parsedTree'
  -------------------------
  -- Sort the parseDecls --
  -------------------------
  p_TypeAlias = V.filter ((0==) . judge) parsedTree
  p_Datas     = V.filter ((1==) . judge) parsedTree
  p_TopBinds  = V.filter ((2==) . judge) parsedTree
  p_TopSigs   = V.filter ((3==) . judge) parsedTree
  p_defaults  = V.filter ((4==) . judge) parsedTree
  -- grouped = V.fromList <$> groupWith judge parsedTree
  judge :: P.Decl -> Int = \case
    P.TypeAlias{}   -> 0
    P.DataDecl{}    -> 1
    P.FunBind{}     -> 2
    P.TypeSigDecl{} -> 3
    _               -> 4 -- P.DefaultDecl{}

  ----------------------
  -- Lookup functions --
  ----------------------
  -- global human name Maps
  freshName :: ToCoreEnv Name = do
    n <- gets nameCount
    modify (\x->x{nameCount = n+1})
    pure n

  hNSigMap :: M.Map T.Text Type = foldl f M.empty p_TopSigs
    where f mp (P.TypeSigDecl nms ty) =
            foldl (\m k->M.insert (pName2Text k) (convTy ty) m) mp nms
  hNGTypeMap = (getDataHName<$>p_Datas) V.++ (getAliasHName<$>p_TypeAlias)
    where getDataHName (P.DataDecl nm _ _)   = pName2Text nm
          getAliasHName = \case P.TypeAlias nm _ -> pName2Text nm
  hNGBindMap = extractHName <$> p_TopBinds
    where extractHName = \case
              P.FunBind matches -> head $ (pName2Text . match2Hnm) <$> matches
          match2Hnm = \case
              P.Match nm pats rhs -> nm
              P.InfixMatch pat nm pats rhs -> nm

  -- HNm->Nm functions
  findGTyHName :: T.Text->Maybe Name = \hNm -> V.findIndex (==hNm) hNGTypeMap
  findGHName :: T.Text->Maybe Name =  \hNm -> V.findIndex (==hNm) hNGBindMap
  -- findSig  = \nm -> V.findIndex (\) p_TopSigs

  --lookupGTy :: Name->Type = \nm -> hNGTypeMap V.! nm
  lookupTy :: Name->TypeMap->Entity = \nm typeMap -> typeMap V.! nm
  lookupBind :: Name->BindMap->BindMap->Binding
   = \nm globalMap localMap -> case compare nm (V.length localMap) of
       LT -> globalMap V.! nm
       _  -> localMap V.! (nm-V.length localMap) 

  -- ToCoreEnv functions
  findSig :: T.Text -> Maybe Type = \hNm -> M.lookup hNm hNSigMap
  findHName :: T.Text -> ToCoreEnv (Maybe Name) =
    \hNm -> gets localHNames >>= \localNames ->
      pure ((localNames M.!? hNm) <|> (findGHName hNm))
  addHName :: T.Text -> Name -> ToCoreEnv () =
    \hNm nm -> modify (\x->x{localHNames = M.insert hNm nm (localHNames x)})

  addLocal :: Name -> Binding -> ToCoreEnv Name =
    \iNm bind -> do
      modify (\x->x{localBinds=V.snoc (localBinds x) bind })
      pure iNm

  ----------
  -- Data --
  ----------
  -- For each data declaration we need:
  --  * TypeName of the data
  --  * GATD style constructor list (term level)
  -- since constructors are handled before topBinds, they get the first names
  (dataEntities, consLists) = V.unzip $ V.imap doData p_Datas
  constructors = V.foldl (V.++) V.empty consLists
  doData :: Name -> P.Decl -> (Entity, V.Vector Binding)
    = \nm -> \case
      P.TypeAlias pName ty -> (entity, consList)
        where entity = Entity (Just hNm) (convTy ty) uniType
              hNm = pName2Text pName
              consList = V.empty -- no constructors for this
      P.DataDecl pName kind qCons -> (entity, consList)
        where hNm = pName2Text pName
              entity = Entity (Just hNm) dataTy uniType
              dataTy = TyUnknown -- qCons2MonoType
              consList = (getCon dataTy . ignoreTyVars) <$> V.fromList qCons
              ignoreTyVars (P.QualConDecl vars condecls) = condecls
              getCon :: Type -> P.ConDecl -> Binding
                = \dataTy -> \case
                P.ConDecl hNm types -> LCon ty
                  where nm = Just $ pName2Text hNm
                        ty = TyArrow (convTy<$>types) dataTy
                P.InfixConDecl tyA hNm tyB -> _
                P.GadtDecl hNm kind tyVars fields -> _

  defaults = M.empty -- map doDefault p_defaults

  --------------
  -- Bindings --
  --------------
  -- topBinds = constructors and top function binds
  -- localBinds is a [Vector Binding] of all local bindings in the module
  topBinds = constructors V.++ topBinds' :: V.Vector Binding
  (ConvState totalNames _ _ localBinds' errors) = endState
  (topBinds', endState) = runState (V.imapM doExpr p_TopBinds) convState
   where convState = ConvState
           { nameCount = V.length p_TopBinds + V.length constructors
           , localHNames    = M.empty
           , localTypeVars  = M.empty
           , localBinds     = V.empty
           , toCoreErrors   = []
           }

  -- doExpr add local bindings to the state and return top bindings
  -- also add errors to the state
  -- ! does P.Match{hNm} match the one in bindMap ?
  doExpr :: Int -> P.Decl -> ToCoreEnv Binding
   = \nm' f@(P.FunBind matches) ->
    let nm = nm' + V.length constructors
        ty = case findSig $ (\(P.Match hNm _ _)->pName2Text hNm) $ (head matches) of
          Nothing -> TyUnknown
          Just t -> t
    in case matches of
        [match] -> match2LBind match ty
        other -> error "please use 'case' expressions"

  -- P.Case PExp [Alt]
  -- Alt Pat Rhs
  -- Convert to case. (expr2Core (P.Case) can optimize it.)
  match2LBind :: P.Match -> Type -> ToCoreEnv Binding = \m ty ->
    let getPatList = \case
            P.Match nm pats rhs -> (nm, pats, rhs)
            P.InfixMatch p1 nm ps rhs -> (nm, (p1:ps), rhs)
        (fNm, pats, rhs) = getPatList m
        mkLArgs :: Name -> P.Pat -> ToCoreEnv Binding = \iNm pat -> do
          hNmMaybe <- case pat of
              P.PVar hNm -> let h = pName2Text hNm
                            in addHName h iNm *> pure (Just h)
              _          -> pure Nothing

          -- TODO use the known type !!
          let bind = LArg $ Entity hNmMaybe TyUnknown 0
          addLocal iNm bind
          pure bind

        unExpr (P.UnGuardedRhs e) = e
        fEntity = Entity (Just $ pName2Text fNm) ty uniTerm
    in do
    iNames <- mapM (\_->freshName) pats
    zipWithM mkLArgs iNames pats
    expr <- expr2Core $ unExpr rhs
    pure $ LBind iNames expr fEntity

  expr2Core :: P.PExp -> ToCoreEnv CoreExpr = \case
    P.Var (P.UnQual hNm)-> findHName (pName2Text hNm) >>= \case
      Just n -> pure $ Var n
      Nothing -> do
         error ("expr2Core: not in scope: " ++ show hNm)
    P.Con pNm-> expr2Core (P.Var pNm) -- same as Var
    P.Lit l -> pure $ Lit $ literal2Core l
    P.Infix nm -> expr2Core (P.Var nm)
    P.App f args -> handlePrecedence f args
      where handlePrecedence f args = App <$> expr2Core f
                                      <*> mapM expr2Core args
    P.Let binds exp -> _
    P.MultiIf _ -> _
    P.Lambda f args -> _
    P.MultiIf alts -> _
    P.Case e alts -> _
    P.Do stmts -> _  -- exprToCore $ foldr1 desugarStmt stmts
   -- suboptimal.. should use the name number corresponding to ">>" and ">>->" for this.
  --  where desugarStmt (P.Qualifier a) (P.Qualifier b) -> App (Var (P.Symbol ">>")) [a, b]
    P.MDo stmts -> _
    P.List f -> _
    P.TypeSig e ty -> _
    P.AsPat nm pat -> _
    P.WildCard -> pure WildCard
    P.TypeExp ty -> _
    P.Typed t e -> _

  pat2Core :: P.Pat -> ToCoreEnv CoreExpr = \case
    P.PVar hNm -> findHName (pName2Text hNm) >>= \case
        Nothing -> error "internal pattern error"
        Just n -> pure $ Var n
    P.PLit l -> pure $ Lit $ literal2Core l
    P.PInfixApp p1 n ps -> do
       a <- pat2Core p1
       b <- pat2Core ps
       pat2Core $ P.PApp n (p1:[ps])
    P.PApp qNm ps -> _
    P.PTuple p -> _
    P.PList ps -> _
    P.PWildCard -> _

literal2Core :: P.Literal -> Literal =
  let mkLit = LlvmLit . LLVM.AST.ConstantOperand
  in mkLit . \case
  P.Char c   -> C.Int 8 $ toInteger $ ord c
  P.Int c    -> C.Int 32 $ c
  P.String c -> _ -- String c
  P.Frac c   -> _
