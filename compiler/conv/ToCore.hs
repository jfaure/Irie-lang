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
-- ! this assumes it is the first to name anything !
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

    -- Records: only difference is we also need to emit accessor functions
--  P.TyRecord hNm fields->MonoTyRecord hNm (doSumAlt prodTyRecord <$> fields)

    -- simple alias
    t -> convTy t >>= \ty -> pure
      (V.empty, Entity (Just $ pName2Text aliasName) ty)

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
    tys <- getFn <$> convTy ty
    pure $ Entity (Just hNm) (TyMono$MonoTyPrim$primCon$prim <$> tys)
  in \case
    P.Extern   nm ty -> addExtern PrimExtern   nm ty
    P.ExternVA nm ty -> addExtern PrimExternVA nm ty

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
  , bindings      = binds
  , externs       = externs
  , overloads     = overloads
  , defaults      = IM.empty
  }
  where
  (binds, dataTys, overloads, externs) = evalState toCoreM convState

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

  -- Setup ToCoreEnv
  convState = ConvState
    { nameCount      = 0 --V.length p_TopBinds -- + V.length constructors
    , tyNameCount    = 0
    , hNames         = M.empty -- incl. types
    , hTyNames       = M.empty -- incl. types

    , localBinds     = V.empty
    , toCoreErrors   = []
    }
  -- :: topBindings ; typeDecls ; localBindings ; overloads ; externs
  -- Note. types and binds vectors must be consistent with iNames
  toCoreM :: ToCoreEnv (BindMap, TypeMap, ClassOverloads, TypeMap) = do
    -- 1. data: get the constructors and dataEntities (name + dataty)
    (cons, dataEntities) <- getTypesAndCons p_TyAlias
    V.imapM (\i (LCon (Entity (Just hNm) _ )) -> addHName hNm i) cons
    -- modify (\x->x{tyNameCount = tyNameCount})
    modify (\x->x{nameCount = V.length cons})

    -- 2. extern entities
    externs <- mapM (doExtern dataEntities) p_externs

    -- 3. type functions:
    --    2Core is easy, we let typeJudge deal with complications
    typeFuns <- mapM doTypeFun p_TyFuns

    -- 4. typeclasses
    -- get: (classFn bindings, classTy polytypes, instance overloads)
    -- note. classDecls includes local bindings (they must match iNames)
    (classDecls, classEntities, overloadBinds)
      <- doTypeClasses p_TyClasses p_TyClassInsts
      :: ToCoreEnv (V.Vector Binding, V.Vector Entity
                    , IM.IntMap (IM.IntMap [P.Decl]))

    -- Generate instance overloads, making sure to match iNames to the binds
    -- we want to use classDecl iNames for our overloads
    let genOverload (P.FunBind [match@(P.Match nm _ _)]) = do
          let fName = pName2Text nm
              sig = TyUnknown
          iNm <- findHName fName <&> \case -- lookup class fn
              Nothing -> error ("unknown class function: " ++ show fName)
              Just i  -> i
          f <- match2LBind match sig
          pure (iNm, f)

    -- double IntMap: InstTyName to (classFn to binding)
    overloads <- mapM (mapM (\insts->IM.fromList <$> mapM genOverload insts)) overloadBinds
      :: ToCoreEnv ClassOverloads -- (IM.IntMap (IM.IntMap Binding))

    --let classOverloads  = IM.fromList <$> classFns
    classLocals <- gets localBinds
    modify (\x->x{localBinds=V.empty})

    -- 5. expression bindings
    -- need to register all names first (for recursive references)
    hNSigMap <- mkSigMap p_TopSigs -- :: ToCoreEnv (M.Map T.Text Type)
    let findTopSig :: HName -> Maybe Type = \hNm -> M.lookup hNm hNSigMap
    fnBinds <- getFns findTopSig p_TopBinds
    fnLocals  <- gets localBinds

    -- 6. Collect results
    -- ! the resulting vectors must be consistent with all iNames !
    let binds = cons V.++ classDecls V.++ classLocals V.++ fnBinds V.++ fnLocals
        tyEntities = dataEntities V.++ classEntities
    pure (binds, tyEntities, overloads, externs)

-- TODO register the tyfun's name
doTypeFun :: P.Decl -> ToCoreEnv TypeFunction
doTypeFun (P.TypeFun nm args expr) = mapM (\_->freshName) args
    >>= \argNms -> case expr of
    P.TypeExp ty -> --trivial type function
        let hNm = pName2Text nm
        in --registerHName hNm *>
           TyTrivialFn argNms <$> convTy ty
    dependent -> TyDependent argNms <$> expr2Core expr

doTypeClasses :: V.Vector P.Decl -> V.Vector P.Decl
 -> ToCoreEnv (V.Vector Binding, V.Vector Entity, IM.IntMap (IM.IntMap [P.Decl]))
doTypeClasses p_TyClasses p_TyClassInsts = do
  -- 2.1 Typeclass top declarations
  let partitionFns = partition $ \case {P.TypeSigDecl{}->True ;_-> False }
      getClassSigs (P.TypeSigDecl nms sig) =
        (\ty -> (\x->LClass$Entity (Just (pName2Text x)) ty)<$>nms)
        <$> convTy sig
      doClass :: (P.Decl) -> ToCoreEnv [Binding]
      doClass (P.TypeClass nm decls) =
          let (sigs, fnBinds) = partitionFns decls
              registerClassFn (P.TypeSigDecl nms sig) =
                mapM (\h -> addHName (pName2Text h) =<< freshName) nms
          in do
             if (length fnBinds > 0)
             then error "default class decls unsupported"
             else pure ()
             -- register all names
             addTyHName (pName2Text nm) =<< freshTyName
             mapM registerClassFn sigs
             -- collect class signatures
             sigMap <- mkSigMap (V.fromList sigs)
             let getSig = (\hNm -> M.lookup hNm sigMap)
             -- TODO default class functions
             -- getFns getSig (V.length dataTys) (V.fromList fnBinds)
             concat <$> mapM getClassSigs sigs
  -- top-level class bindings, we add these to the bindmap.
  -- Instance functions are added to the 'OverLoads intmap'
  -- These take polytypes; typeJudge will have to instantiate them.
  classDecls <- V.fromList . concat <$> mapM doClass p_TyClasses
    :: ToCoreEnv (V.Vector Binding)

  -- 2.1 TypeClass overloads/instances
  -- For each typeclass, we're constructing it's (poly)type, and collecting
  -- it's overloads: We fold classInsts, and simultaneously check them.
  -- We also need to update the typeclass PolyType every instance
  let f :: P.Decl -> IM.IntMap  (Type, IM.IntMap [P.Decl])
        -> ToCoreEnv (IM.IntMap (Type, IM.IntMap [P.Decl]))
      f tcInst@(P.TypeClassInst clsNm instTyNm decls) classIMap =
        let ok = check p_TyClasses tcInst
            (clsHNm, instHNm) = (pName2Text clsNm, pName2Text instTyNm)
            (sigs, fnBinds)   = partitionFns decls
            declsOk = not $ any (\case P.FunBind{}->False ; _ -> True) fnBinds
            -- verify that inst satisfies the class decl
            check classes inst = True
            addPoly (TyPoly (ForallOr tys)) t = (TyPoly (ForallOr (t:tys)))
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
        let polyTy = TyPoly (ForallOr [TyAlias instINm])
            val = (polyTy, IM.singleton instINm fnBinds)
            insertFn (ty', binds') (ty, binds)
              = (addPoly ty' ty, IM.union binds binds') -- union may fail ?
            newMp = IM.insertWith insertFn clsINm val classIMap
        pure newMp

  -- The classIMap contains both the class polytypes and class overloads
  classIMap <- foldrM f IM.empty p_TyClassInsts
    :: ToCoreEnv (IM.IntMap (Type, IM.IntMap [P.Decl]))

  -- Get class Entities (a polytype for each typeclass var)
  let classTys = fst <$> IM.elems classIMap
      overloadBinds = snd <$> classIMap

      toEntity i ty =
          let ent = (\(LClass info) -> named info) $ classDecls V.! i
              hNm = case ent of
                Nothing -> error "internal error: lost class typeName"
                Just n -> n
          in Entity (Just hNm) ty
  let classEntities = V.imap toEntity (V.fromList classTys)

  -- Results = class entities: The polytype associated with each class
  -- Overloads = all instance functions
  -- note. delay generating overloads, let toCoreM handle iNames
  pure (classDecls, classEntities, overloadBinds)

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
