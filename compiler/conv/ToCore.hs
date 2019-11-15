-- convert parse tree to core

-- 1. (resolve infix apps (including precedence)) n. do this in seperate pass
-- 2. convert all HNames to INames
-- * desugar PExpr to CoreExpr
module ToCore
where

import Prim
import CoreSyn
import qualified CoreUtils as CU
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
import Data.Functor

import Debug.Trace

-- TODO use Data.hashMap.Strict | Data.IntMap.
-- conversion state is necessary when converting variables to integers
type ToCoreEnv a = State ConvState a
data ConvState = ConvState {
   nameCount     :: IName
 , tyNameCount   :: IName

 , hNames        :: HM.HashMap HName IName
 , hTyNames      :: HM.HashMap HName IName

 , localTys      :: V.Vector Entity
 , localBinds    :: V.Vector Binding
 , toCoreErrors  :: [ToCoreErrors]
}
type ToCoreErrors = String

-- incomplete function ?
pName2Text = \case
  P.Ident h -> T.pack h
  P.Symbol s -> T.pack s
pQName2Text (P.UnQual (P.Ident s)) = T.pack s

------------
-- ConvTy --
------------
data ConvTyError
 = UnknownTy    HName
 | UnknownTyVar HName
 | UnexpectedTy P.Type

-- Error handling is slightly different if the ty is in a type function
convTy :: (HName -> Maybe IName) -> P.Type -> Either ConvTyError Type
 = \findNm ->
 let convTy' = convTy findNm
 in \case
  P.TyPrim t                -> Right$TyMono$MonoTyPrim t
  P.TyPoly (P.PolyAnd   f)-> TyPoly . PolyConstrain <$> mapM convTy' f
  P.TyPoly (P.PolyUnion f) -> TyPoly . PolyUnion     <$> mapM convTy' f
  P.TyPoly (P.PolyAny)  -> Right$TyPoly$PolyAny
  P.TyName n                ->
  -- A TyName is either an alias or a data !
    let hNm = pName2Text n in case findNm hNm of
      Just iNm -> Right $ TyAlias iNm
      Nothing ->  Left (UnknownTy hNm)
  -- TODO only in tyfunctions..
  P.TyVar n   -> let hNm = pName2Text n in case findNm hNm of
      Just iNm -> Right $ TyAlias iNm
      Nothing  -> Left (UnknownTyVar hNm)
  P.TyArrow tys'             -> TyArrow <$> mapM convTy' tys'
  P.TyExpr e                 -> _ -- TyExpr $ expr2Core e
  P.TyTyped a b              -> _ -- suspect
  P.TyUnknown                -> Right $ TyUnknown
  t                          -> Left $ UnexpectedTy t

-- Default behavior for top level type signatures,
-- new variables are implicitly quantified
convTyM :: P.Type -> ToCoreEnv Type = \pTy ->
  mkFindTyHName <&> (`convTy` pTy) >>= \case
  Right ty -> pure ty
  Left  er -> case er of
    UnknownTy ty    -> error ("unknown typeName: " ++ show ty)
    UnknownTyVar ty -> --error ("unknown typeName: " ++ show ty)
      withNewTyHNames [ty] $ \[ty] -> convTyM pTy
    UnexpectedTy t  -> case t of
      P.TyApp tfn targs -> do
        fn <- convTyM tfn
        args <- mapM convTyM targs
        pure $ TyExpr $ TyApp fn args
      _ -> error ("unexpected ty: "    ++ show t)

doTypeFun :: P.Decl -> IName -> ToCoreEnv TypeFunction
doTypeFun (P.TypeFun nm args expr) tyFunINm =
  let tyFnhNm = pName2Text nm
      argHNms = pName2Text <$> args
  in do
  addTyHName tyFnhNm tyFunINm
  withNewTyHNames argHNms $ \argNms -> case expr of
    P.TypeExp ty -> do --trivial type function
        zipWithM addTyHName argHNms argNms
        tyEither <- mkFindTyHName <&> (`convTy` ty)
        tyBody   <- case tyEither of
          Right t -> pure t
          Left (UnexpectedTy dty@(P.TyData alts)) -> do
            dataNm <- freshName
            (cons, dataTy, subTys) <- convData dataNm (P.TypeAlias nm dty)
            modify (\x->x{localBinds= localBinds x V.++ cons})
            modify (\x->x{localTys= (localTys x `V.snoc` dataTy) V.++ subTys})
            pure $ typed dataTy
          _ -> error "bad tyfunction"
        pure $ TyTrivialFn argNms tyBody

    dependent -> TyDependent argNms <$> expr2Core expr

----------
-- Data --
----------
-- ! this assumes it is the first to name anything !
getTypesAndCons :: V.Vector P.Decl -- .TypeAlias
  -> ToCoreEnv (V.Vector Binding, V.Vector Entity)
 = \datas ->
  -- type/data names may be used out of order/recursively
  -- note. convTy converts all P.TyName to TyAlias
  let registerData iNm (P.TypeAlias qNm ty) = addTyHName (pName2Text qNm) iNm
  in do
  iNms <- V.fromList <$> freshTyNames (V.length datas)
  V.zipWithM registerData iNms datas
  sumCons_monoTys_pairs <- V.zipWithM convData iNms datas
  let (cons, ents, localEnts) = V.unzip3 sumCons_monoTys_pairs
  let vConcat = foldr (V.++) V.empty
  pure (vConcat cons, ents V.++ vConcat localEnts)

-- Convert one Data decl to (constructors, dataType ++ subTypes)
-- input must be TypeAlias.
-- Sum types are polytype alts of their product types
convData :: IName -> P.Decl
         -> ToCoreEnv (V.Vector Binding, Entity, V.Vector Entity)
 = \dataINm (P.TypeAlias aliasName ty) ->
  let dataNm = pName2Text aliasName
  in case ty of
  P.TyData sumTys -> do
      let go :: (P.Name, [P.Type]) -> ToCoreEnv (HName, [Type])
          go (prodNm, tupleTys) = do
              coreTys <- mapM convTyM tupleTys
              pure (pName2Text prodNm, coreTys)
      (conHNames, conTys) <- unzip <$> mapM go sumTys
      let nAlts = length conHNames

      conINames <- freshNames nAlts
      zipWithM addHName conHNames conINames

      -- Make subtypes
      let qual             = dataNm `T.snoc` '.'
          subTyHNames      = (qual `T.append`) <$> conHNames
      subTyINames <- freshTyNames nAlts
      zipWithM addTyHName subTyHNames subTyINames
      let subTypes         = TyMono . MonoRigid <$> subTyINames
          mkSubEnts hNm ty = Entity (Just hNm) ty
          subEnts          = V.fromList$zipWith mkSubEnts subTyHNames subTypes
      let dataDef          = DataDef dataNm (zip conHNames conTys)
          dataPolyType     = PolyData (PolyUnion subTypes) dataDef
          dataEnt          = Entity (Just dataNm) (TyPoly dataPolyType)

      let f prodNm prodTy subTy = LCon $ Entity (Just prodNm) $
            (TyArrow $ prodTy ++ [subTy])
          cons = V.fromList $ zipWith3 f conHNames conTys subTypes
      pure (cons, dataEnt, subEnts)

    -- Records: only difference is we also need to emit accessor functions
--  P.TyRecord hNm fields->MonoTyRecord hNm (doSumAlt prodTyRecord <$> fields)

  -- simple alias
  t -> convTyM t >>= \ty -> pure
      (V.empty, Entity (Just $ pName2Text aliasName) ty, V.empty)

-- getFns: generate bindings from a [P.Decl]
-- both normal fns and typeclass funs use this
getFns :: (HName->Maybe Type) -> V.Vector P.Decl -> ToCoreEnv (V.Vector Binding)
getFns findSig fnBindings =
  let registerBinds :: (HName->Maybe Type) -> P.Decl
                    -> ToCoreEnv (P.Match, Type)
      registerBinds findSig (P.FunBind [match]) =
          let getHName (P.Match nm _ _) = pName2Text nm
              getHName _ = error "please use 'case' expressions"
              hNm = getHName $ match
              ty = case findSig hNm of
                  Nothing -> TyUnknown
                  Just t -> t
          in do
          addHName hNm =<< freshName
          pure (match, ty)
      registerBinds s what = error ("cannot register: " ++ show what)
  in do
  (matches, tys) <- V.unzip <$> V.mapM (registerBinds findSig) fnBindings
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
  in pats2Bind pats rhsE (Just (pName2Text fNm)) fnSig

pats2Bind :: [P.Pat] -> P.PExp -> Maybe HName -> Type -> ToCoreEnv Binding
pats2Bind pats rhsE fNm fnSig = do
  -- special case for scopedtypevars: lift typed expr to fn sig
  (ty, pExp) <- case (fnSig, rhsE) of
      (TyUnknown, P.Typed t e) -> (,e) <$> convTyM t
      _ -> pure (fnSig, rhsE)

  iNames <- mapM (\_->freshName) pats
  zipWithM mkLArg iNames pats
  expr <- expr2Core $ pExp
  pure $ LBind iNames expr (Entity fNm ty)

mkSigMap :: V.Vector P.Decl -> ToCoreEnv (M.Map HName Type)
mkSigMap sigs =
    let f (P.TypeSigDecl nms ty) mp = convTyM ty >>= \t ->
            pure $ foldr (\k m->M.insert (pName2Text k) t m) mp nms
    in foldrM f M.empty sigs

doExtern :: TypeMap -> P.Decl -> ToCoreEnv Entity
doExtern tyMap = let
  addExtern primCon nm ty = 
    let hNm = pName2Text nm
        getFn (TyArrow tys) = tys
        getFn _ = error "only functions can be externs"
        prim (CU.unVar tyMap -> TyMono (MonoTyPrim p)) = p
        prim t = error ("only primtypes allowed in externs: " ++ show t)
    in do
    freshName >>= addHName (pName2Text nm)
    tys <- getFn <$> convTyM ty
    let externTy = TyMono $ MonoTyPrim $ primCon $ prim <$> tys
    pure $ Entity (Just hNm) externTy
  in \case
    P.Extern   nm ty -> addExtern PrimExtern   nm ty
    P.ExternVA nm ty -> addExtern PrimExternVA nm ty

------------------------------
-- Various lookup functions --
------------------------------
freshNames :: Int -> ToCoreEnv [IName] = \count ->
  gets nameCount >>= \n ->
  modify (\x -> x{nameCount = n+count})   *> pure [n..n+count-1]
freshTyNames :: Int -> ToCoreEnv [IName] = \count ->
  gets tyNameCount >>= \n ->
  modify (\x -> x{tyNameCount = n+count}) *> pure [n..n+count-1]
freshName :: ToCoreEnv IName = gets nameCount >>= \n ->
  modify (\x->x{nameCount = n+1}) *> pure n
freshTyName :: ToCoreEnv IName = gets tyNameCount >>= \n ->
  modify (\x->x{tyNameCount = n+1}) *> pure n

-- ToCoreEnv functions
addHName    :: T.Text -> IName -> ToCoreEnv () = \hNm nm ->
  modify (\x->x{hNames = HM.insert hNm nm (hNames x)})
addTyHName  :: T.Text -> IName -> ToCoreEnv () =
  \hNm nm -> modify (\x->x{hTyNames = HM.insert hNm nm (hTyNames x)})
-- add local names
withNewHNames  :: [HName] -> ([IName] -> ToCoreEnv a) -> ToCoreEnv a
withNewHNames =
  \hNms fn -> CU.localState $ do
    iNms <- freshNames (length hNms)
    zipWithM addHName hNms iNms
    fn iNms
withNewTyHNames :: [HName] -> ([IName] -> ToCoreEnv a) -> ToCoreEnv a
withNewTyHNames =
  \hNms fn -> CU.localState $ do
    iNms <- freshTyNames (length hNms)
    zipWithM addTyHName hNms iNms
    fn iNms
findHName   :: HName -> ToCoreEnv (Maybe IName) =
  \hNm    -> gets hNames >>= \nms -> pure (hNm `HM.lookup` nms)
findTyHName :: HName -> ToCoreEnv (Maybe IName) =
  \hNm    -> gets hTyNames >>= \nms -> pure (hNm `HM.lookup` nms)

mkFindHName, mkFindTyHName :: ToCoreEnv (HName -> Maybe IName)
mkFindHName   = gets hNames   >>= \nms -> pure (`HM.lookup` nms)
mkFindTyHName = gets hTyNames >>= \nms -> pure (`HM.lookup` nms)

addLocal    :: IName -> Binding -> ToCoreEnv IName =
  \iNm bind -> do
    modify (\x->x{localBinds=V.snoc (localBinds x) bind })
    pure iNm

------------------------
-- Main conv function --
------------------------
parseTree2Core :: P.Module -> CoreModule
parseTree2Core parsedTree = CoreModule
  { algData       = dataTys -- data entites from 'data' declarations
  , bindings      = binds
  , externs       = externs
  , overloads     = overloads
  , defaults      = IM.empty
  }
  where
  (binds, dataTys, overloads, externs) = evalState toCoreM $ ConvState
    { nameCount      = 0
    , tyNameCount    = 0
    , hNames         = HM.empty
    , hTyNames       = HM.empty

    , localBinds     = V.empty
    , localTys       = V.empty
    , toCoreErrors   = []
    }

  --------------------------
  -- Group the parseDecls --
  --------------------------
  -- Would be nice to have subtyping for this
  mapTuple9 z (a,b,c,d,e,f,g,h,i) = (z a,z b,z c,z d,z e,z f,z g,z h,z i)
  (p_TyAlias, p_TyFuns, p_TyClasses, p_TyClassInsts
    , p_TopSigs, p_TopBinds, p_InfixBinds
    , p_defaults, p_externs) = mapTuple9 V.fromList groupDecls
   where
   groupDecls = foldr f ([],[],[],[],[],[],[],[],[]) parsedTree
   f x (a,b,c,d,e,f,g,h,i) = case x of
    P.TypeAlias{}     -> (x:a,b,c,d,e,f,g,h,i)
    P.TypeFun{}       -> (a,x:b,c,d,e,f,g,h,i)
    P.TypeClass{}     -> (a,b,x:c,d,e,f,g,h,i)
    P.TypeClassInst{} -> (a,b,c,x:d,e,f,g,h,i)

    P.TypeSigDecl{}   -> (a,b,c,d,x:e,f,g,h,i)
    P.FunBind{}       -> (a,b,c,d,e,x:f,g,h,i)
    P.InfixDecl{}     -> (a,b,c,d,e,f,x:g,h,i)

    P.DefaultDecl{}   -> (a,b,c,d,e,f,g,x:h,i)
    P.Extern{}        -> (a,b,c,d,e,f,g,h,x:i)
    P.ExternVA{}      -> (a,b,c,d,e,f,g,h,x:i)

  -- :: topBindings ; typeDecls ; localBindings ; overloads ; externs
  -- Note. types and binds vectors must be consistent with iNames
  toCoreM :: ToCoreEnv (BindMap, TypeMap, ClassOverloads, TypeMap) = do
    -- 1. data: get the constructors and dataEntities (name + dataty)
    (cons, dataEntities) <- getTypesAndCons p_TyAlias

    -- 2. extern entities
    externs <- mapM (doExtern dataEntities) p_externs
    let externBinds = LExtern <$> externs

    -- 3. type functions:
    tyFunINms <- V.fromList <$> freshNames (V.length p_TyFuns)
    typeFuns  <- V.zipWithM doTypeFun p_TyFuns tyFunINms
    traceShowM typeFuns

    -- 4. typeclasses
    -- we need: (classFn bindings, classTy polytypes, instance overloads)
    -- note. classDecls includes local bindings (they must match iNames)
    (classDecls, classEntities, overloadBinds)
      <- doTypeClasses p_TyClasses p_TyClassInsts
    -- Overloads :: (IM.IntMap (IM.IntMap Binding))
    overloads   <- generateOverloads overloadBinds :: ToCoreEnv ClassOverloads
    classLocals <- gets localBinds
    modify (\x->x{localBinds=V.empty})

    -- 5. expression bindings
    -- need to register all names first (for recursive references)
    hNSigMap <- mkSigMap p_TopSigs -- :: ToCoreEnv (M.Map T.Text Type)
    let findTopSig :: HName -> Maybe Type = \hNm -> M.lookup hNm hNSigMap
    fnBinds  <- getFns findTopSig p_TopBinds
    fnLocals <- gets localBinds

    -- 6. Collect results
    -- ! the resulting vectors must be consistent with all iNames !
    let binds = V.concat
          [cons, externBinds, classDecls, classLocals, fnBinds, fnLocals]
        tyEntities = dataEntities V.++ classEntities
    pure (binds, tyEntities, overloads, externs)

generateOverloads :: IM.IntMap (IM.IntMap [P.Decl]) -> ToCoreEnv ClassOverloads
 = \overloadBinds ->
  -- Generate instance overloads, making sure to match iNames to the binds
  let genOverload (P.FunBind [match@(P.Match nm _ _)]) =
        let fName = pName2Text nm
            sig = TyUnknown
        in do
        iNm <- findHName fName <&> \case -- lookup class fn
            Nothing -> error ("unknown class function: " ++ show fName)
            Just i  -> i
        f <- match2LBind match sig
        pure (iNm, f)
  in
  -- double IntMap: InstTyName to (classFn to binding)
  mapM (mapM (\insts->IM.fromList <$> mapM genOverload insts)) overloadBinds


doTypeClasses :: V.Vector P.Decl -> V.Vector P.Decl
 -> ToCoreEnv (V.Vector Binding, V.Vector Entity, IM.IntMap (IM.IntMap [P.Decl]))
doTypeClasses p_TyClasses p_TyClassInsts = do
  -- 2.1 Typeclass top declarations
  let partitionFns = partition $ \case {P.TypeSigDecl{}->True ;_-> False }
      getClassSigs (P.TypeSigDecl nms sig) =
        (\ty -> (\x->LClass$Entity (Just (pName2Text x)) ty)<$>nms)
        <$> convTyM sig
      doClass :: (P.Decl) -> ToCoreEnv (HName, [Binding])
      doClass (P.TypeClass nm decls) =
          let (sigs, fnBinds) = partitionFns decls
              registerClassFn (P.TypeSigDecl nms sig) =
                mapM (\h -> addHName (pName2Text h) =<< freshName) nms
          in do
             if (length fnBinds > 0)
             then error "default class decls unsupported"
             else pure ()
             -- register all names
             classTyINm <- freshTyName
             let classTyHNm = pName2Text nm
             addTyHName classTyHNm classTyINm
             mapM registerClassFn sigs
             -- collect class signatures
             sigMap <- mkSigMap (V.fromList sigs)
             let getSig = (\hNm -> M.lookup hNm sigMap)
             -- TODO default class functions
             -- getFns getSig (V.length dataTys) (V.fromList fnBinds)
             (classTyHNm,) . concat <$> mapM getClassSigs sigs
  -- top-level class bindings, we add these to the bindmap.
  -- Instance functions are added to the 'OverLoads intmap'
  -- These take polytypes; typeJudge will have to instantiate them.
  (classTyNms, classDecls') <- V.unzip <$> V.mapM doClass p_TyClasses
    :: ToCoreEnv (V.Vector HName,  V.Vector [Binding])
  let classDecls = V.fromList $ V.foldr (++) [] classDecls'

  -- 2.1 TypeClass overloads/instances
  -- For each typeclass, we're constructing it's (poly)type, and collecting
  -- it's overloads: We fold classInsts, and simultaneously check them.
  -- We also need to update the typeclass PolyType every instance
  let f :: P.Decl -> IM.IntMap  (PolyType, IM.IntMap [P.Decl])
        -> ToCoreEnv (IM.IntMap (PolyType, IM.IntMap [P.Decl]))
      f tcInst@(P.TypeClassInst clsNm instTyNm decls) classIMap =
        let ok = check p_TyClasses tcInst
            (clsHNm, instHNm) = (pName2Text clsNm, pName2Text instTyNm)
            (sigs, fnBinds)   = partitionFns decls
            declsOk = not $ any (\case P.FunBind{}->False ; _ -> True) fnBinds
            -- verify that inst satisfies the class decl
            check classes inst = True
            addPoly (PolyUnion t1) (PolyUnion t2) = (PolyUnion (t2 ++ t1))
        in if not $ ok && declsOk -- TODO better validity checks
        then error "bad instance decl"
        else do

        -- check names exist
        clsINm  <- findTyHName clsHNm <&> \case
          Just h -> h
          Nothing -> error ("instance for unknown class: " ++ show clsHNm)
        instINm  <- findTyHName instHNm <&> \case
          Just h -> h
          Nothing -> error ("instance for unknown class: " ++ show clsHNm)

        -- get instance signatures
        instSigMap <- mkSigMap (V.fromList sigs)
        let findInstSig hNm = M.lookup hNm instSigMap
            findClassSig :: HName -> HName -> Maybe Type
              -- TODO generate signatures from classSigs (replace classNm)
              = \fnName instTyNm -> Nothing
            getSig nm = findInstSig nm -- <|> findClassSig nm instHNm
              --case getSig fName of
              --Nothing -> error ("no sig for instance: " ++ show nm)
              --Just t  -> t
        let polyTy = PolyUnion [TyAlias instINm]
            val = (polyTy, IM.singleton instINm fnBinds)
            insertFn (ty', binds') (ty, binds)
              = (addPoly ty' ty, IM.union binds binds') -- union may fail ?
            newMp = IM.insertWith insertFn clsINm val classIMap
        pure newMp

  -- The classIMap contains both the class polytypes and class overloads
  classIMap <- foldrM f IM.empty p_TyClassInsts
    :: ToCoreEnv (IM.IntMap (PolyType, IM.IntMap [P.Decl]))

  -- Get class Entities (a polytype for each typeclass var)
  let classTys = TyPoly <$> fst <$> IM.elems classIMap
      overloadBinds = snd <$> classIMap
      toEntity hNm ty = Entity (Just hNm) ty
  let classEntities = V.zipWith toEntity classTyNms (V.fromList classTys)

  -- Results = class entities: The polytype associated with each class
  -- Overloads = all instance functions
  -- note. delay generating overloads, let toCoreM handle iNames
  pure (classDecls, classEntities, overloadBinds)

expr2Core :: P.PExp -> ToCoreEnv CoreExpr = \case
  P.Var (P.UnQual hNm)-> findHName (pName2Text hNm) >>= \case
      Just n -> pure $ Var n
      Nothing -> do error ("expr2Core: not in scope: " ++ show hNm)
  P.Con pNm           -> expr2Core (P.Var pNm) -- same as Var
  P.Lit l             -> do
    iNm <- freshName
    maybeTy  <- findTyHName $ T.pack $ case l of
        Char   c -> "Num"
        Int    i -> "Num"
        Frac   r -> "Num"
        String s -> "CharPtr"
        Array lits -> "CharPtr"
    let ty = case maybeTy of
            Nothing -> error "Internal: prim typeclass not in scope"
            Just t  -> TyAlias t
    addLocal iNm (LBind [] (Lit l) (Entity Nothing ty))
    pure $ Var iNm

  P.PrimOp primInstr  -> pure $ Instr primInstr
  P.Infix nm          -> expr2Core (P.Var nm)
  P.App f args        -> handlePrecedence f args
    where handlePrecedence f args = App <$> expr2Core f
                                    <*> mapM expr2Core args

  -- let|lambda: need to lift functions to ToCoreEnv
  -- P.Let Binds PExp where Binds = BDecls [Decl]
  -- P.Lambda [Pat] PExp
  -- TODO allow any decl ?
  -- TODO use M.insertlookupWithkey to restore squashed values later !
  P.Let binds exp   -> _ -- local decls !!
-- withNewHNames  :: [HName] -> ([IName] -> ToCoreEnv a)
--                -> ToCoreEnv a

  -- lambdas are Cases with 1 alt
  -- TODO similar to match2Lbind !
  --match2LBind :: P.Match -> Type -> ToCoreEnv Binding = \m fnSig ->
  P.Lambda pats f   -> do
      fIName <- freshName
      bind <- pats2Bind pats f (Nothing) TyUnknown
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
  P.TypeExp ty   -> TypeExpr <$> convTyM ty
  P.Typed t e    -> do -- we name it so we can type annotate it
      iNm <- freshName
      ty <- convTyM t
      expr <- expr2Core e
      addLocal iNm (LBind [] expr (Entity Nothing ty))
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
