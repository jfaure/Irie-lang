-- convert parse tree to core

-- 1. (resolve infix apps (including precedence)) n. do this in seperate pass
-- 2. convert all HNames to INames
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

import Data.Char (ord)
import Data.Foldable (foldrM)
import Control.Monad (zipWithM)
import Control.Applicative ((<|>))

import Debug.Trace

-- conversion state is necessary when converting variables to integers
type ToCoreEnv a = State ConvState a
data ConvState = ConvState {
   nameCount     :: Name

  -- local/global name maps
 , hNames        :: M.Map HName IName
 , typeHNames    :: M.Map HName IName

 , localBinds    :: V.Vector Binding
 , toCoreErrors  :: [ToCoreErrors]
}
type ToCoreErrors = String

-- incomplete function
pName2Text = \case
  P.Ident h -> T.pack h
  P.Symbol s -> T.pack s
pQName2Text (P.UnQual (P.Ident s)) = T.pack s

-- convTy requires TCEnv monad to handle type variables
convTy :: P.Type -> ToCoreEnv Type
 = \case
  P.TyLlvm l                 -> pure $ TyMono (MonoTyLlvm l)
  P.TyForall (P.ForallAnd f) -> pure . TyPoly . ForallAnd =<< mapM convTy f
  P.TyForall (P.ForallOr f)  -> pure . TyPoly . ForallOr  =<< mapM convTy f
  P.TyForall (P.ForallAny)   -> pure $ TyPoly $ ForallAny
  P.TyName n                 -> do
    let hNm = pName2Text n -- TODO add name
    findHName hNm >>= \case
      Just iNm -> pure (TyVar iNm)
      Nothing ->  error ("unknown typeName: " ++ show hNm)
  P.TyArrow tys'             -> do
    tys <- mapM convTy tys'
    let args = init tys
        retTy = last tys
    pure $ TyArrow args retTy
  P.TyExpr e                 -> _ -- TyExpr $ expr2Core e
  P.TyTyped a b              -> _
  P.TyUnknown                -> pure TyUnknown

----------
-- Data --
----------
-- For each data declaration we need:
--  * TypeName of the data
--  * GATD style constructor list (term level)
-- since constructors are handled before topBinds, they get the first names
-- ! this assumes it has naming priority [0..], so it must be first !
getTypesAndCons :: V.Vector P.Decl
  -> ToCoreEnv (V.Vector Entity, V.Vector Binding)
getTypesAndCons datas = do
  let registerData :: IName -> P.Decl -> ToCoreEnv Entity
      registerData iNm (P.DataDecl qNm kind cons) = do
          let hNm = pName2Text qNm
          addHName hNm iNm
          pure $ Entity (Just hNm) (TyMono (MonoTyData iNm)) uniType

  -- do top level names first (they may be used out of order/recursively)
  typeEntities <- V.imapM (registerData) datas
  consLists <- V.zipWithM (\d e -> data2Bindings d (typed e)) datas typeEntities
  let cons = V.foldl (V.++) V.empty consLists
  pure (typeEntities, cons)

-- return all constructors for the data
data2Bindings :: P.Decl -> Type -> ToCoreEnv (V.Vector Binding)
data2Bindings (P.DataDecl pName kind qCons) dataTy = do
  let unInfix :: P.ConDecl -> P.ConDecl = \case
          P.InfixConDecl tyA hNm tyB -> P.ConDecl hNm [tyA, tyB]
          P.GadtDecl hNm kind tyVars fields -> _
          other -> other
      ignoreTyVars (P.QualConDecl vars condecls) = condecls
      con2Bind (P.ConDecl qNm types) = do
          tys <- mapM convTy types
          let ty = TyArrow tys dataTy
          pure $ LCon $ Entity (Just (pName2Text qNm)) ty uniTerm
  let doCon = con2Bind . unInfix . ignoreTyVars
      constructors = mapM doCon (V.fromList qCons)
  constructors

--doAliases :: P.Decl -> Entity
--doAliases (P.TypeAlias pName ty) = entity
--  where entity = Entity (Just hNm) (convTy ty) uniType
--        hNm = pName2Text pName

------------------------------
-- Various lookup functions --
------------------------------
--lookupGTy :: Name->Type = \nm -> hNGTypeMap V.! nm
lookupTy :: IName->TypeMap->Entity = \nm typeMap -> typeMap V.! nm
lookupBind :: IName->BindMap->BindMap->Binding
 = \nm globalMap localMap -> case compare nm (V.length localMap) of
     LT -> globalMap V.! nm
     _  -> localMap V.! (nm-V.length localMap) 

-- ToCoreEnv functions
findHName :: HName -> ToCoreEnv (Maybe Name) =
  \hNm -> gets hNames >>= \localNames ->
    pure (localNames M.!? hNm) -- <|> (findGHName hNm))
addHName :: T.Text -> Name -> ToCoreEnv () =
-- TODO use M.insertlookupWithkey to restore squashed values later !
  \hNm nm -> modify (\x->x{hNames = M.insert hNm nm (hNames x)})

addLocal :: IName -> Binding -> ToCoreEnv Name =
  \iNm bind -> do
    modify (\x->x{localBinds=V.snoc (localBinds x) bind })
    pure iNm

------------------------
-- Main conv function --
------------------------
parseTree2Core :: P.Module -> CoreModule
parseTree2Core parsedTree' = CoreModule
  { algData       = dataTys -- data entites from 'data' declarations
  , bindings      = topBinds V.++ (localBinds endState)
  , defaults      = M.empty
  }
  where
  parsedTree  = V.fromList parsedTree'
  -------------------------
  -- Sort the parseDecls --
  -------------------------
  -- quite ugly, but better than using 5 filters
  (p_TypeAlias, p_Datas, p_TopBinds, p_TopSigs, p_defaults) =
    (\(a,b,c,d,e)->
    (V.fromList a,V.fromList b,V.fromList c,V.fromList d,V.fromList e))
    $ groupDecls
   where 
   groupDecls = foldr f ([],[],[],[],[]) parsedTree'
   f x (a,b,c,d,e) = case x of
    P.TypeAlias{}   -> (x:a,b,c,d,e)
    P.DataDecl{}    -> (a,x:b,c,d,e)
    P.FunBind{}     -> (a,b,x:c,d,e)
    P.TypeSigDecl{} -> (a,b,c,x:d,e)
    _               -> (a,b,c,d,x:e)

  ----------------------
  -- Lookup functions --
  ----------------------
  -- global human name Maps
  freshName :: ToCoreEnv Name = do
    n <- gets nameCount
    modify (\x->x{nameCount = n+1})
    pure n

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

  -- Setup ToCoreEnv
  convState = ConvState
    { nameCount      = V.length p_TopBinds -- + V.length constructors
    , hNames         = M.empty
--  , typeHNames     = M.empty

    , localBinds     = V.empty
    , toCoreErrors   = []
    }
  toCoreM :: ToCoreEnv (BindMap, V.Vector Entity,  ExprMap) = do
    -- 1. data
    -- register the hnames for constructors - we need to do this after
    -- giving a name to all the constructor types
    (dataTys, cons) <- getTypesAndCons p_Datas
    mapM (\(LCon (Entity (Just hNm) _ _ )) -> freshName >>= addHName hNm) cons

    -- 2. type signatures
    -- super important is to reserve the lower names for top bindings
    -- (so we can directly index the top bind_map later)
    modify (\x->x{nameCount = nameCount x + V.length p_TopBinds})
    let f (P.TypeSigDecl nms ty) mp = convTy ty >>= \t ->
            pure $ foldr (\k m->M.insert (pName2Text k) t m) mp nms
    hNSigMap <- foldrM f M.empty p_TopSigs -- :: ToCoreEnv (M.Map T.Text Type)
    let findSig :: HName -> Maybe Type = \hNm -> M.lookup hNm hNSigMap

    -- 3. expression bindings
    -- need to register all names first (for recursive references)
    let registerBinds :: IName -> P.Decl -> ToCoreEnv (P.Match, Type)
        registerBinds iNm (P.FunBind [match]) = do
          let getHName (P.Match nm _ _) = pName2Text nm
              getHName _ = error "please use 'case' expressions"
              hNm = getHName $ match
              ty = case findSig hNm of
                  Nothing -> TyUnknown
                  Just t -> t
          addHName hNm iNm
          pure (match, ty)
    (matches, tys) <- V.unzip <$> V.imapM registerBinds p_TopBinds
    fnBinds <- V.zipWithM match2LBind matches tys

    -- 4. join constructors with topExprs (and locals ?)
    let topBinds = cons V.++ fnBinds  -- the order is critical !
    locals <- gets localBinds
    pure (topBinds, dataTys, locals)

  ( (topBinds, dataTys, locals) ,
    endState
    ) = runState toCoreM convState

  -- convert function matches to top level binding
  -- note. (P.Case PExp [Alt]) ; Alt Pat Rhs
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
    P.Lambda f args -> _
      -- addLocal i (LBind args expr (Entity (Just hNm) TyUnknown 0)))
    P.MultiIf alts -> _ -- a SwitchCase on 'True' value

    -- TODO multi param case expression ?
    P.Case pe alts -> do -- Alt = Alt Pat Rhs
      e <- expr2Core pe

      -- dataCase: all alts have type (Name [Name] expr)
      -- then it's a data decomposition
      let alts2DataCase :: ToCoreEnv [Maybe (Name, [Name], CoreExpr)]
            = mapM go alts
          varOrNothing (P.PVar n) = Just (pName2Text n)
          varOrNothing _          = Nothing
          go (P.Alt pat (P.UnGuardedRhs pexp)) = do
            let p = doInfixPats pat
            case p of
              P.PVar hNm -> findHName (pName2Text hNm) >>= \case
                 Nothing -> error ("unknown name in pattern: " ++ show hNm)
                 Just n -> expr2Core pexp >>= \exp ->
                      pure $ Just (n, [], exp)
              P.PApp hNm argPats -> findHName (pQName2Text hNm) >>= \case
                 Nothing -> error ("unknown Constructor:" ++ show hNm)
                 Just n  -> do
                   -- check they're all Just
                   let args = case sequence (varOrNothing <$> argPats) of
                                Just x -> x
                                Nothing -> error "failed to convert pattern"
                   iArgs <- mapM (\_ -> freshName) args
                   zipWithM (\i hNm -> (addHName hNm i)
                             *> addLocal i (LArg (Entity (Just hNm) TyUnknown 0)))
                            iArgs args
                   exp <- expr2Core pexp
                   pure $ Just (n, iArgs, exp)
              _ -> pure Nothing
          --  P.PVar hNm -> _
          --  P.PLit l -> _
          --  P.PTuple p -> _
          --  P.PList ps -> _
          --  P.PWildCard -> _

      dataCase <- sequence <$> alts2DataCase
      -- switchCase: all alts must be literlas
      let litAlts = _ -- no switchCase for now

      pure $ case dataCase of
        Just alts -> DataCase e alts
        Nothing   -> SwitchCase e litAlts

    P.Do stmts -> _
    P.MDo stmts -> _
    P.List f -> _
    P.TypeSig e ty -> _
    P.AsPat nm pat -> _
    P.WildCard -> pure WildCard
    P.TypeExp ty -> _
    P.Typed t e -> _

  -- handle infix patterns
  doInfixPats :: P.Pat -> P.Pat = \case
    P.PInfixApp p1 n ps ->
      let a = doInfixPats p1
          b = doInfixPats ps
      in doInfixPats $ P.PApp n (p1:[ps])
    P.PApp qNm ps -> P.PApp qNm (doInfixPats <$> ps)
    other -> other

literal2Core :: P.Literal -> Literal =
  let mkLit = LlvmLit . LLVM.AST.ConstantOperand
      mkChar c = C.Int 8 $ toInteger $ ord c 
  in mkLit . \case
  P.Char c   -> mkChar c
  P.Int i    -> C.Int 32 $ i
  P.String s -> C.Array (LLVM.AST.IntegerType 8) (mkChar <$> s)
  P.Frac f   -> _
