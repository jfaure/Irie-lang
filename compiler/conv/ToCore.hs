-- convert parse tree to core

-- 1. (resolve infix apps (including precedence)) n. do this in seperate pass
-- 2. convert all HNames to INames
-- * desugar PExpr to CoreExpr

{-# OPTIONS -fdefer-typed-holes -Wno-typed-holes #-}
module ToCore
where

import Prim
import CoreSyn
import qualified ParseSyntax as P

import qualified Data.Vector         as V
import qualified Data.Text           as T
import qualified Data.Map.Strict     as M
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict  as IM
import Control.Monad.Trans.State.Strict
import Data.List (partition)
import Data.Foldable (foldrM)
import Control.Monad (zipWithM)
import Control.Applicative ((<|>))

import Debug.Trace

-- TODO use Data.hashMap.Strict | Data.IntMap.
-- conversion state is necessary when converting variables to integers
type ToCoreEnv a = State ConvState a
data ConvState = ConvState {
   nameCount     :: IName
 , tyNameCount   :: IName

 , hNames        :: M.Map HName IName
 , hTyNames      :: M.Map HName IName

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
    findTyHName hNm >>= \case
      Just iNm -> pure $ TyAlias iNm
      Nothing ->  error ("unknown typeName: " ++ show hNm)
  P.TyArrow tys'             -> do
    tys <- mapM convTy tys'
    pure $ TyArrow tys
  P.TyExpr e                 -> _ -- TyExpr $ expr2Core e
  P.TyTyped a b              -> _ -- suspect
  P.TyUnknown                -> pure TyUnknown

----------
-- Data --
----------
getTypesAndCons :: V.Vector P.Decl -- .TypeAlias
  -> ToCoreEnv (V.Vector Binding, V.Vector Entity)
 = \datas ->
  -- type/data names may be used out of order/recursively
  -- note. convTy converts all P.TyName to TyAlias
  let registerData iNm (P.TypeAlias qNm ty) = addTyHName (pName2Text qNm) iNm
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

      let f prodNm prodTy = LCon$Entity (Just prodNm) (TyArrow prodTy)
          cons = V.fromList $ zipWith f prodHNames prodTys

          tyNm = pName2Text dataNm
          ty = TyMono $ MonoTyData tyNm (zip prodHNames prodTys)
          ent = Entity (Just tyNm) ty
          getSubTypes (prodNm,_) =
            let nm = pQName2Text (P.QName [dataNm] prodNm)
            in  TyAlias <$> freshTyName
--    subTypeAliases <- getSubTypes <$> sumTys
--    let polyEnt = Entity (Just tyNm) (TyPoly (ForallOr subTypeAliases))
--    pure (cons, polyEnt)
      pure (cons, ent)

    -- simple alias
    t -> convTy t >>= \ty -> pure
      (V.empty, Entity (Just $ pName2Text aliasName) ty)

  --P.TyRecord hNm fields->MonoTyRecord hNm (doSumAlt prodTyRecord <$> fields)

-- getFns: generate bindings from a [P.Decl]
-- both normal fns and typeclass funs use this
getFns :: (HName->Maybe Type) -> Int -> V.Vector P.Decl -> ToCoreEnv (V.Vector Binding)
getFns findSig usedNames fnBindings = do
  let registerBinds :: (HName->Maybe Type) -> IName -> P.Decl
                    -> ToCoreEnv (P.Match, Type)
      registerBinds findSig iNm (P.FunBind [match]) = do
        let getHName (P.Match nm _ _) = pName2Text nm
            getHName _ = error "please use 'case' expressions"
            hNm = getHName $ match
            ty = case findSig hNm of
                Nothing -> TyUnknown
                Just t -> t
        addHName hNm (iNm + usedNames)
        pure (match, ty)
      registerBinds s i what = error ("cannot register: " ++ show what)
  (matches, tys) <- V.unzip
    <$> V.imapM (registerBinds findSig) fnBindings
  V.zipWithM match2LBind matches tys

-- Convert fn argument patterns to case expr (for lambdas + matches)
-- TODO handle more patterns
mkLArg :: IName -> P.Pat -> ToCoreEnv Binding = \iNm pat -> do
  hNmMaybe <- case pat of
      P.PVar hNm -> let h = pName2Text hNm
                    in addHName h iNm *> pure (Just h)
      _          -> pure Nothing
  -- in some cases we could give the type immediately,
  -- but in general we must leave that to typeJudge
  let bind = LArg $ Entity hNmMaybe TyUnknown
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
  zipWithM mkLArg iNames pats
  expr <- expr2Core $ pExp
  let fEntity = Entity (Just $ pName2Text fNm) ty
  pure $ LBind iNames expr fEntity

mkSigMap :: V.Vector P.Decl -> ToCoreEnv (M.Map HName Type)
mkSigMap sigs = 
    let f (P.TypeSigDecl nms ty) mp = convTy ty >>= \t ->
            pure $ foldr (\k m->M.insert (pName2Text k) t m) mp nms
    in foldrM f M.empty sigs

------------------------------
-- Various lookup functions --
------------------------------
freshNames :: Int -> ToCoreEnv [IName] = \count ->
  gets nameCount >>= \n ->
  modify (\x -> x{nameCount = n+count}) *> pure [n..n+count-1]
freshTyNames :: Int -> ToCoreEnv [IName] = \count ->
  gets nameCount >>= \n ->
  modify (\x -> x{nameCount = n+count}) *> pure [n..n+count-1]

freshName :: ToCoreEnv IName = gets nameCount >>= \n ->
  modify (\x->x{nameCount = n+1}) *> pure n
freshTyName :: ToCoreEnv IName = gets tyNameCount >>= \n ->
  modify (\x->x{tyNameCount = n+1}) *> pure n

lookupTy :: IName->TypeMap->Entity = \nm typeMap -> typeMap V.! nm
lookupBind :: IName->BindMap->BindMap->Binding
 = \nm globalMap localMap -> case compare nm (V.length localMap) of
     LT -> globalMap V.! nm
     _  -> localMap V.! (nm-V.length localMap)

-- ToCoreEnv functions
-- TODO use M.insertlookupWithkey to restore squashed values later !
addHName :: T.Text -> IName -> ToCoreEnv () =
  \hNm nm -> modify (\x->x{hNames = M.insert hNm nm (hNames x)})
addTyHName :: T.Text -> IName -> ToCoreEnv () =
  \hNm nm -> modify (\x->x{hTyNames = M.insert hNm nm (hTyNames x)})
findHName :: HName -> ToCoreEnv (Maybe IName) =
  \hNm -> gets hNames >>= \nms -> pure (nms M.!? hNm)
findTyHName :: HName -> ToCoreEnv (Maybe IName) =
  \hNm -> gets hTyNames >>= \nms -> pure (nms M.!? hNm)

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
parseTree2Core parsedTree = CoreModule
  { algData       = dataTys -- data entites from 'data' declarations
  , bindings      = topBinds V.++ (localBinds endState)
  , overLoads     = IM.empty
  , defaults      = IM.empty
  }
  where
  -------------------------
  -- Sort the parseDecls --
  -------------------------
  mapTuple8 z (a,b,c,d,e,f,g,h) = (z a,z b,z c,z d,z e,z f,z g,z h)
  (p_TyAlias, p_TyFuns, p_TyClasses, p_TyClassInsts
    , p_TopSigs, p_TopBinds, p_InfixBinds
    , p_defaults) = mapTuple8 V.fromList groupDecls
   where
   groupDecls = foldr f ([],[],[],[],[],[],[],[]) parsedTree
   f x (a,b,c,d,e,f,g,h) = case x of
    P.TypeAlias{}     -> (x:a,b,c,d,e,f,g,h)
    P.TypeFun{}       -> (a,x:b,c,d,e,f,g,h)
    P.TypeClass{}     -> (a,b,x:c,d,e,f,g,h)
    P.TypeClassInst{} -> (a,b,c,x:d,e,f,g,h)

    P.TypeSigDecl{}   -> (a,b,c,d,x:e,f,g,h)
    P.FunBind{}       -> (a,b,c,d,e,x:f,g,h)
    P.InfixDecl{}     -> (a,b,c,d,e,f,x:g,h)

    P.DefaultDecl{}   -> (a,b,c,d,e,f,g,x:h)

  -- Setup ToCoreEnv
  convState = ConvState
    { nameCount      = 0 --V.length p_TopBinds -- + V.length constructors
    , tyNameCount    = 0
    , hNames         = M.empty -- incl. types
    , hTyNames       = M.empty -- incl. types

    , localBinds     = V.empty
    , toCoreErrors   = []
    }
  -- toCoreM returns globals, types, locals
  toCoreM :: ToCoreEnv (BindMap, TypeMap, BindMap) = do
    -- data ; tyFuns ; tySigs ; bindings
    -- 1. data
    -- gen the constructors and dataTys, and name the constructors
    (cons, dataTys) <- getTypesAndCons p_TyAlias
    V.imapM (\i (LCon (Entity (Just hNm) _ )) -> addHName hNm i) cons
    let nameCount = V.length cons
    -- modify (\x->x{nameCount = V.length cons})

    -- 2.1 Typeclass top declarations
    let partitionFns = partition $ \case {P.TypeSigDecl{}->True ;_-> False }
        getClassSigs (P.TypeSigDecl nms sig) =
          (\ty -> (\x->LClass$Entity (Just (pName2Text x)) ty)<$>nms)
          <$> convTy sig
        doClass :: (P.Decl) -> ToCoreEnv [Binding]
        doClass (P.TypeClass nm decls) =
            let (sigs, fnBinds) = partitionFns decls
            in do 
               if (length fnBinds > 0)
               then error "default class decls unsupported"
               else pure ()
               i <- freshTyName
               addTyHName (pName2Text nm) i
               sigMap <- mkSigMap (V.fromList sigs)
               let getSig = (\hNm -> M.lookup hNm sigMap)
               -- TODO default class functions
               -- getFns getSig (V.length dataTys) (V.fromList fnBinds)
               concat <$> mapM getClassSigs sigs

    -- top-level class bindings, we add these to the bindmap.
    -- Instance functions are added to the 'OverLoads intmap'
    -- These take polytypes; typeJudge will have to instantiate them.
    classDecls <- V.fromList . concat <$> mapM doClass p_TyClasses

    -- 2.1 TypeClass overloads/instances
    -- TODO better validity checks
    -- Plan is to fold over classInsts, checking validity along the way
    -- We also need to update the typeclass PolyType every instance
    let f :: P.Decl -> (M.Map IName Type, V.Vector Binding)
          -> ToCoreEnv ((M.Map IName Type), V.Vector Binding)
        f tcInst@(P.TypeClassInst clsNm instTyNm decls) (polyTypesMap, fns) =
          let ok = check p_TyClasses tcInst
              clsHNm = pName2Text clsNm
              (sigs, fnBinds) = partitionFns decls
              declsOk = not $ any (\case P.FunBind{}->False ; _ -> True) fnBinds
              val = TyPoly (ForallOr [TyAlias 0])
              addPoly (TyPoly (ForallOr tys)) t = (TyPoly (ForallOr (t:tys)))
          in if not $ ok && declsOk
          then error "bad instance decl"
          else do
          sigMap <- mkSigMap (V.fromList sigs)
          let findInstSig :: HName -> Maybe Type = \hNm -> M.lookup hNm sigMap
              findClassSig :: HName -> HName -> Maybe Type
                = \fnName instTyNm -> Nothing -- TODO
              getSig nm = findInstSig nm <|> findClassSig nm (pName2Text instTyNm)

          fnBinds <- getFns getSig 0 (V.fromList fnBinds)
          clsINm  <- (<$> findTyHName clsHNm) $ \case
            Just h -> h
            Nothing -> error ("instance for unknown class: " ++ show clsHNm)
          let accFns = fnBinds V.++ fns
              newMp = M.insertWith addPoly clsINm val polyTypesMap
          pure (newMp, accFns)

        check classes inst = True -- verify that inst satisfies the class decl (ie. only fn sigs, fn binds)

    -- TODO we will have multiple function defs of different types, how to handle that ?
    -- * we want to emit only class type sigs (where the classTy is a polytype of all implementations)
    -- + a type function for each instance
    --registerClassFns
    (classTyMap, instFns) <- foldrM f (M.empty, V.empty) p_TyClassInsts
--  let classEntities = (\(hNm, ty) -> Entity (Just hNm) ty) <$> M.assocs classTyMap

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
    hNSigMap <- mkSigMap p_TopSigs -- :: ToCoreEnv (M.Map T.Text Type)
    let findTopSig :: HName -> Maybe Type = \hNm -> M.lookup hNm hNSigMap

    -- 5. expression bindings
    -- need to register all names first (for recursive references)
    modify (\x->x{nameCount = V.length p_TopBinds + V.length cons})
    fnBinds <- getFns findTopSig (V.length cons) p_TopBinds

    -- 6. join constructors with topExprs (and locals ?)
    -- locals may be functions we need to lift !
    -- ! the order is critical, it must match iNames !
    let topBinds = cons V.++ classDecls V.++ fnBinds
    let tyEntities = dataTys
    locals <- gets localBinds
    pure (topBinds, dataTys, locals)

  ( (topBinds, dataTys, locals) ,
    endState
    ) = runState toCoreM convState

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
  -- TODO allow any decl ?
  P.Let binds exp   -> _ -- local decls !!

  -- lambdas are Cases with 1 alt
  -- TODO similar to match2Lbind !
  P.Lambda pats f   -> do
      fIName <- freshName
      iArgs  <- mapM (\_ -> freshName) pats
      zipWithM mkLArg iArgs pats
      expr <- expr2Core f
      let bind = LBind iArgs expr (Entity Nothing TyUnknown)
      addLocal fIName bind
      pure $ Var fIName

  P.LambdaCase alts -> do
      fIName <- freshName
      iArg   <- freshName
      expr   <- getCaseAlts alts (Var iArg)
      let bind = LBind [iArg] expr (Entity Nothing TyUnknown)
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
--      f :: ((PExp,PExp) -> CoreExpr.SwitchCase -> CoreExpr.SwitchCase)
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
      addLocal iNm (LArg (Entity Nothing ty))
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
                         *> addLocal i (LArg (Entity (Just hNm) TyUnknown)))
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
