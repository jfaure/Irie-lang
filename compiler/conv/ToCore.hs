-- convert parse tree to core

-- 1. (resolve infix apps (including precedence)) n. do this in seperate pass
-- 2. convert all HNames to INames
-- * desugar PExpr to CoreExpr

{-# LANGUAGE LambdaCase, ScopedTypeVariables, MultiWayIf #-}
{-# OPTIONS -fdefer-typed-holes -Wno-typed-holes #-}
module ToCore
where

import Prim
import CoreSyn
import qualified ParseSyntax as P

import qualified Data.Vector as V
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Control.Monad.Trans.State.Strict

import Data.Foldable (foldrM)
import Control.Monad (zipWithM)
import Control.Applicative ((<|>))

import Debug.Trace

-- conversion state is necessary when converting variables to integers
type ToCoreEnv a = State ConvState a
data ConvState = ConvState {
   nameCount     :: IName

 , hNames        :: M.Map HName IName
 --, hNameTypes    :: M.Map HName IName

 , localBinds    :: V.Vector Binding
 , toCoreErrors  :: [ToCoreErrors]
}
type ToCoreErrors = String

-- incomplete function ?
pName2Text = \case
  P.Ident h -> T.pack h
  P.Symbol s -> T.pack s
pQName2Text (P.UnQual (P.Ident s)) = T.pack s

-- the only legitimate TyVars are data + tyAliases
-- other tyVars are arguments of type functions
-- this needs to be effectful to handle tyVar lookup errors
convTy :: P.Type -> ToCoreEnv Type
 = \case
  P.TyPrim t                 -> pure $ TyMono $ MonoTyPrim t
  P.TyForall (P.ForallAnd f) -> pure . TyPoly . ForallAnd=<<mapM convTy f
  P.TyForall (P.ForallOr f)  -> pure . TyPoly . ForallOr =<<mapM convTy f
  P.TyForall (P.ForallAny)   -> pure $ TyPoly $ ForallAny
  P.TyName n                 -> do
  -- A TyName is either an alias or a data !
    let hNm = pName2Text n
    findHName hNm >>= \case
      Just iNm -> pure $ TyAlias iNm
      Nothing ->  error ("unknown typeName: " ++ show hNm)
  P.TyArrow tys'             -> do
    tys <- mapM convTy tys'
    pure $ TyArrow tys
  P.TyExpr e                 -> _ -- TyExpr $ expr2Core e
  P.TyTyped a b              -> _
  P.TyUnknown                -> pure TyUnknown

----------
-- Data --
----------
-- ! this assumes it has naming priority [0..], so it must be first !
getTypesAndCons :: V.Vector P.Decl -- .TypeAlias
  -> ToCoreEnv (V.Vector Binding, V.Vector Entity)
 = \datas ->
  -- type/data names may be used out of order/recursively
  -- note. convTy converts all P.TyName to TyAlias
  let registerData iNm (P.TypeAlias qNm ty) = addHName (pName2Text qNm) iNm
  in do
  V.imapM_ registerData datas
  sumCons_monoTy_pairs <- mapM convData datas
  let constructors = foldr (V.++) V.empty $ fst <$> sumCons_monoTy_pairs
      dataMonoTys =                         snd <$> sumCons_monoTy_pairs
  pure (constructors, dataMonoTys)

-- * collect constructors and make a type for the data
-- Convert one Data decl to CoreSyn
-- Entity.typed is always a MonoTyData
-- input should only be TypeAlias to Data !
convData :: P.Decl -> ToCoreEnv (V.Vector Binding, Entity)
 = \(P.TypeAlias aliasName ty) ->
  case ty of
    P.TyData sumTys -> let dataNm = aliasName in do
      let go :: (P.Name, [P.Type]) -> ToCoreEnv (HName, [Type])
          go (prodNm, prodTys) = do
              coreTys <- mapM convTy prodTys
              pure (pName2Text prodNm, coreTys)

      (prodHNames, prodTys) <- unzip <$> mapM go sumTys

      let f prodNm prodTy = LCon$Entity (Just prodNm) (TyArrow prodTy) 0
          cons = V.fromList $ zipWith f prodHNames prodTys

          tyNm = pName2Text dataNm
          ty = TyMono $ MonoTyData tyNm (zip prodHNames prodTys)
          ent = Entity (Just tyNm) ty 1
      pure (cons, ent)

    -- simple alias
    t -> convTy t >>= \ty -> pure
      (V.empty, Entity (Just $ pName2Text aliasName) ty 0)

  --P.TyRecord hNm fields->MonoTyRecord hNm (doSumAlt prodTyRecord <$> fields)

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
findHName :: HName -> ToCoreEnv (Maybe IName) =
  \hNm -> gets hNames >>= \localNames ->
    pure (localNames M.!? hNm) -- <|> (findGHName hNm))
addHName :: T.Text -> IName -> ToCoreEnv () =
-- TODO use M.insertlookupWithkey to restore squashed values later !
  \hNm nm -> modify (\x->x{hNames = M.insert hNm nm (hNames x)})

addLocal :: IName -> Binding -> ToCoreEnv IName =
  \iNm bind -> do
    modify (\x->x{localBinds=V.snoc (localBinds x) bind })
    pure iNm

-- TODO [Decls] must be parsable within coreexpr, but :: Decl -> CoreModule
-- So do let bindings create a local module that imports all bindings at that
-- point ? we could then inline that module
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
  (p_TyAlias, p_TyFuns, p_TopBinds, p_TopSigs, p_defaults) =
    (\(a,b,c,d,e)->
    (V.fromList a,V.fromList b,V.fromList c,V.fromList d,V.fromList e))
    $ groupDecls
   where
   groupDecls = foldr f ([],[],[],[],[]) parsedTree'
   f x (a,b,c,d,e) = case x of
    P.TypeAlias{}   -> (x:a,b,c,d,e)
    P.TypeFun{}     -> (a,x:b,c,d,e)
    P.FunBind{}     -> (a,b,x:c,d,e)
    P.TypeSigDecl{} -> (a,b,c,x:d,e)
    P.DefaultDecl{} -> (a,b,c,d,x:e)

  ----------------------
  -- Lookup functions --
  ----------------------
  -- global human name Maps
  freshName :: ToCoreEnv IName = do
    n <- gets nameCount
    modify (\x->x{nameCount = n+1})
    pure n

  -- TODO order !
  hNGTypeMap :: V.Vector HName
   = (getDataHName<$>p_TyFuns) V.++ (getAliasHName<$>p_TyAlias)
    where getDataHName (P.TypeFun nm _ _)   = pName2Text nm
          getAliasHName = \case P.TypeAlias nm _ -> pName2Text nm

  hNGBindMap :: V.Vector HName
   = extractHName <$> p_TopBinds
    where extractHName = \case
              P.FunBind matches -> head $ (pName2Text . match2Hnm) <$> matches
          match2Hnm = \case
              P.Match nm pats rhs -> nm
              P.InfixMatch pat nm pats rhs -> nm

  -- HNm->Nm functions
  findGTyHName :: T.Text->Maybe IName = \hNm -> V.findIndex (==hNm) hNGTypeMap
  findGHName :: T.Text->Maybe IName =  \hNm -> V.findIndex (==hNm) hNGBindMap

  -- Setup ToCoreEnv
  convState = ConvState
    { nameCount      = 0 --V.length p_TopBinds -- + V.length constructors
    , hNames         = M.empty -- incl. types

    , localBinds     = V.empty
    , toCoreErrors   = []
    }
  -- toCoreM returns globals, types, locals
  toCoreM :: ToCoreEnv (BindMap, TypeMap, BindMap) = do
    -- 1. Typeclasses
    -- These are simply polytypes: TyPoly, still we must
    -- * check that instances satisfy the class declaration
    -- * function overloading ?
    -- * data overloading ?

    -- data ; tyFuns ; tySigs ; bindings
    -- 2. data
    -- gen the constructors and dataTys, and name the constructors
    (cons, dataTys) <- getTypesAndCons p_TyAlias
    V.imapM (\i (LCon (Entity (Just hNm) _ _ )) -> addHName hNm i) cons

    -- 3. type functions
    --    * dependent types are at this point simply converted via convExpr
    --    * trivial qualified data is recognized here
    --    TODO register the tyfun's name
    let doTypeFun :: P.Decl -> ToCoreEnv TypeFunction
        doTypeFun (P.TypeFun nm args expr) = mapM (\_->freshName) args
            >>= \argNms -> case expr of
            P.TypeExp ty -> --trivial type function
                let hNm = pName2Text nm
                in --registerHName hNm *>
                   TyTrivialFn argNms <$> convTy ty
            dependent -> TyDependent argNms <$> expr2Core expr
    typeFuns <- mapM doTypeFun p_TyFuns

    -- 4. type signatures
    let f (P.TypeSigDecl nms ty) mp = convTy ty >>= \t ->
            pure $ foldr (\k m->M.insert (pName2Text k) t m) mp nms
    hNSigMap <- foldrM f M.empty p_TopSigs -- :: ToCoreEnv (M.Map T.Text Type)
    let findSig :: HName -> Maybe Type = \hNm -> M.lookup hNm hNSigMap

    -- 5. expression bindings
    -- need to register all names first (for recursive references)
    let registerBinds :: IName -> P.Decl -> ToCoreEnv (P.Match, Type)
        registerBinds iNm (P.FunBind [match]) = do
          let getHName (P.Match nm _ _) = pName2Text nm
              getHName _ = error "please use 'case' expressions"
              hNm = getHName $ match
              ty = case findSig hNm of
                  Nothing -> TyUnknown
                  Just t -> t
          addHName hNm (iNm + V.length cons)
          pure (match, ty)
    modify (\x->x{nameCount = V.length p_TopBinds + V.length cons})
    (matches, tys) <- V.unzip <$> V.imapM registerBinds p_TopBinds
    fnBinds <- V.zipWithM match2LBind matches tys

    -- 6. join constructors with topExprs (and locals ?)
    -- locals may be functions we need to lift !
    let topBinds = cons V.++ fnBinds  -- the order is critical !
    locals <- gets localBinds
    pure (topBinds, dataTys, locals)

  ( (topBinds, dataTys, locals) ,
    endState
    ) = runState toCoreM convState

  -- Convert fn argument patterns to case expr (for lambdas + matches)
  mkLArgs :: IName -> P.Pat -> ToCoreEnv Binding = \iNm pat -> do
    hNmMaybe <- case pat of
        P.PVar hNm -> let h = pName2Text hNm
                      in addHName h iNm *> pure (Just h)
        _          -> pure Nothing

    -- TODO handle more patterns
    -- in some cases we could give the type immediately,
    -- but in general we must leave that to typeJudge
    let bind = LArg $ Entity hNmMaybe TyUnknown 0
    addLocal iNm bind
    pure bind

  -- convert function matches to top level binding
  -- note. (P.Case PExp [Alt]) ; Alt Pat Rhs
  -- Convert to case. (expr2Core (P.Case) can optimize it.)
  match2LBind :: P.Match -> Type -> ToCoreEnv Binding = \m fnSig ->
    let getPatList = \case
            P.Match nm pats rhs -> (nm, pats, rhs)
            P.InfixMatch p1 nm ps rhs -> (nm, (p1:ps), rhs)
        (fNm, pats, rhs) = getPatList m
        -- TODO GuardedRhs
        unExpr (P.UnGuardedRhs e) = e
        rhsE = unExpr rhs

    in do
    -- special case for scopedtypevars: lift typed expr to fn sig
    (ty, pExp) <- case (fnSig, rhsE) of
        (TyUnknown, P.Typed t e) -> (,e) <$> convTy t
        _ -> pure (fnSig, rhsE)

    iNames <- mapM (\_->freshName) pats
    zipWithM mkLArgs iNames pats
    expr <- expr2Core $ pExp
    let fEntity = Entity (Just $ pName2Text fNm) ty uniTerm
    pure $ LBind iNames expr fEntity

  expr2Core :: P.PExp -> ToCoreEnv CoreExpr = \case
    P.Var (P.UnQual hNm)-> findHName (pName2Text hNm) >>= \case
        Just n -> pure $ Var n
        Nothing -> do error ("expr2Core: not in scope: " ++ show hNm)
    P.Con pNm           -> expr2Core (P.Var pNm) -- same as Var
    P.Lit l             -> pure $ Lit $ l
    P.PrimOp primInstr  -> pure $ Instr primInstr
    P.Infix nm          -> expr2Core (P.Var nm)
    P.App f args        -> handlePrecedence f args
      where handlePrecedence f args = App <$> expr2Core f
                                      <*> mapM expr2Core args

    -- let|lambda: need to lift functions to ToCoreEnv
    -- P.Let Binds PExp where Binds = BDecls [Decl]
    -- P.Lambda [Pat] PExp
    P.Let binds exp   -> _ -- local decls !!

    -- lambdas are Cases with 1 alt
    -- TODO similar to match2Lbind !
    P.Lambda pats f   -> do
        fIName <- freshName
        iArgs  <- mapM (\_ -> freshName) pats
        zipWithM mkLArgs iArgs pats
        expr <- expr2Core f
        let bind = LBind iArgs expr (Entity Nothing TyUnknown 0)
        addLocal fIName bind
        pure $ Var fIName

    P.LambdaCase alts -> do
        fIName <- freshName
        iArg   <- freshName
        expr   <- getCaseAlts alts (Var iArg)
        let bind = LBind [iArg] expr (Entity Nothing TyUnknown 0)
        addLocal fIName bind
        pure $ Var fIName

    -- [(PExp, PExp)]
    P.MultiIf allAlts    ->
           -- split off the last alt to allow us to fold it
      let (lastIfE, lastElseE) = last allAlts
          alts = init allAlts
          (lTrue, lFalse) = (Int 1, Int 0)
          mkSwitch ifE thenE elseAlt = do
            ifE'   <- expr2Core ifE
            thenE' <- expr2Core thenE
            pure $ SwitchCase ifE' [(lTrue, thenE'), elseAlt]
--        f :: ((PExp,PExp) -> CoreExpr.SwitchCase -> CoreExpr.SwitchCase)
          f (ifE, thenE) nextSwitch = mkSwitch ifE thenE (lFalse, nextSwitch)
      in mkSwitch lastIfE lastElseE (lFalse, WildCard) >>= \lastSwitch ->
         foldrM f lastSwitch alts

    P.Case e alts  -> expr2Core e >>= getCaseAlts alts
    P.AsPat nm pat -> _
    P.WildCard     -> pure WildCard
    P.TypeExp ty   -> TypeExpr <$> convTy ty
    P.Typed t e    -> do -- we name it so we can type annotate it
        iNm <- freshName
        ty <- convTy t
        addLocal iNm (LArg (Entity Nothing ty 0))
        pure $ Var iNm

  -- getCaseAlts returns a partial constructor for a CoreExpr.*Case expression
  -- biggest point is to accomodate both P.Case and P.LambdaCase cleanly
  -- There are many patterns to handle here, and it is often necessary
  -- to chain case expressions
  getCaseAlts :: [P.Alt] -> CoreExpr -> ToCoreEnv CoreExpr
   = \alts e -> do
    -- dataCase: all alts have type (Name [Name] expr)
    -- then it's a data decomposition
    let alts2DataCase :: ToCoreEnv [Maybe (IName, [IName], CoreExpr)]
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
  --        P.PVar hNm -> _
  --        P.PLit l -> _
  --        P.PTuple p -> _
  --        P.PList ps -> _
  --        P.PWildCard -> _

    dataCase <- sequence <$> alts2DataCase
    -- switchCase: all alts must be literals
    let litAlts = _ -- no switchCase for now

    pure $ case dataCase of
      Just alts -> DataCase   e alts
      Nothing   -> SwitchCase e litAlts

    where
    -- handle infix patterns
    doInfixPats :: P.Pat -> P.Pat = \case
      P.PInfixApp p1 n ps ->
        let a = doInfixPats p1
            b = doInfixPats ps
        in doInfixPats $ P.PApp n (p1:[ps])
      P.PApp qNm ps -> P.PApp qNm (doInfixPats <$> ps)
      other -> other
