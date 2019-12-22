-- ParseTree -> Core

-- 1. construct vectors for bindings, types and classes
-- 2. resolve infix apps (including precedence)
-- 3. convert all HNames to INames (indexes into vectors)
-- 4. desugar language expressions
module ToCore (parseTree2Core)
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
import Data.Foldable
import GHC.Exts (groupWith)
import Debug.Trace

transpose []             = []
transpose ([]   : xss)   = transpose xss
transpose ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])

type ToCoreEnv a = State ConvState a
data ConvState = ConvState {
   imports       :: V.Vector CoreModule --Imports -- imports in scope
 , localFixities :: HM.HashMap HName Fixity
 , nameCount     :: IName
 , tyNameCount   :: IName

 , hNames        :: HM.HashMap HName IName
 , hTyNames      :: HM.HashMap HName IName

 , _tyList       :: [V.Vector Entity]
 , _bindList     :: [V.Vector Binding]
-- , _defaults     :: IM.IntMap MonoType

-- , localTys      :: V.Vector Entity
 , localBinds    :: V.Vector Binding
 , localModules  :: [CoreModule]
 , toCoreErrors  :: ToCoreErrors
}

--data Imports = Imports [CoreModule] (HM.HashMap HName CoreModule)
--   openImports :: [CoreModule]
-- , qualImports :: HM.HashMap HName CoreModule
-- -- hiding / renaming imports ?
--}

data ToCoreErrors = ToCoreErrors {
   notInScope :: [P.Name]
}
noErrors = ToCoreErrors []

-- incomplete function ?
pName2Text = \case
  P.Ident h  -> h
  P.Symbol s -> s
pQName2Text (P.UnQual (P.Ident s)) = s
pQName2Text (P.UnQual (P.Symbol s)) = s

------------
-- ConvTy --
------------
data ConvTyError
 = UnknownTy    HName
 | UnknownTyVar HName
 | UnexpectedTy P.Type

-- Error handling is different if the ty is in a type function
convTy :: (HName -> Maybe IName) -> P.Type -> Either ConvTyError Type
 = \findNm ->
 let convTy' = convTy findNm
 in \case
  P.TyPrim t               -> Right$TyMono$MonoTyPrim t
  P.TyPoly (P.PolyAnd   f) -> TyPoly . PolyConstrain <$> mapM convTy' f
  P.TyPoly (P.PolyUnion f) -> TyPoly . PolyUnion     <$> mapM convTy' f
  P.TyPoly (P.PolyAny)     -> Right $ TyPoly $ PolyAny
  P.TySet                  -> Right $ TyPoly $ PolyAny
  P.TyName n ->
  -- A TyName is either an alias or a data !
    let hNm = pName2Text n in case findNm hNm of
      Just iNm -> Right $ TyAlias iNm
      Nothing ->  Left (UnknownTy hNm)
  -- TODO only in tyfunctions..
  P.TyVar n   -> let hNm = pName2Text n in case findNm hNm of
      Just iNm -> Right $ TyAlias iNm
      Nothing  -> Left (UnknownTyVar hNm)
  P.TyArrow tys'             -> TyArrow <$> mapM convTy' tys'
  P.TyApp ty tys             -> do
    ty' <- convTy' ty
    tys' <- mapM convTy' tys
    pure $ TyCon ty' tys'
  P.TyExpr e                 -> _ -- TyExpr $ expr2Core e
  P.TyTyped a b              -> _ -- suspect
  P.TyUnknown                -> Right $ TyUnknown
  t                          -> Left  $ UnexpectedTy t

-- Default behavior for top level type signatures,
-- new variables are implicitly quantified
convTyM :: P.Type -> ToCoreEnv Type = \pTy ->
  mkFindTyHName <&> (`convTy` pTy) >>= \case
  Right ty -> pure ty
  Left  er -> case er of
    UnknownTy ty    -> error ("unknown typeName: " ++ show ty)
    UnknownTyVar ty -> do --error ("unknown typeName: " ++ show ty)
    -- register the names - they're implicit foralls
      nm <- freshTyName
      addTyHName ty nm
      addLocalTy nm $ Entity Nothing (TyRigid nm)
      convTyM pTy
--    withNewTyHNames [ty] $ \[ty] -> convTyM pTy
    UnexpectedTy t  -> case t of
      _ -> error ("unexpected ty: "    ++ show t)

-- type constructors
-- We may come accross data definitions at the leaves
-- return tyfuns + data they return

doTypeFun :: P.Decl -> IName -> ToCoreEnv (Entity , V.Vector Entity)
doTypeFun (P.TypeFun topNm args (P.TypeExp ty)) tyFunINm =
  doTyFun (pName2Text topNm) tyFunINm (pName2Text <$> V.fromList args) ty

doTyFun :: HName -> IName -> V.Vector HName -> P.Type
        -> ToCoreEnv (Entity , V.Vector Entity)
doTyFun tyFnHNm tyFunINm argHNms ty = do
  addTyHName tyFnHNm tyFunINm
  argNms <- freshTyNames (length argHNms)
  let rigidTys = TyRigid <$> argNms
      rigids   = (\ty -> Entity Nothing ty) <$> rigidTys

  V.zipWithM addTyHName argHNms (V.fromList argNms)
  rhs <- (`convTy` ty) <$> mkFindTyHName
  (fnBody , cons , subTys) <- case rhs of
    Right t -> pure (t , V.empty , V.empty)
    Left (UnexpectedTy dataDef@(P.TyRecord alts)) -> do
      -- handle TyCons returning data
      (cons, dTy, subTys) <- _convData tyFunINm tyFnHNm dataDef
      pure $ (typed dTy , cons , subTys)
    Left t -> error $ "unexpected return type of tyFunction: "
  mapM rmTyHName argHNms

  let tyFn = TyTrivialFn argNms fnBody
      tyEnt = Entity (Just tyFnHNm) (TyExpr tyFn)

  -- if TyFun returns data, wrap it's constructor types
  let mkTyFn ty = TyExpr $ TyTrivialFn argNms ty
      dataCon2TyFun (LCon ent) =
        LCon ent{ typed = mkTyFn (typed ent) }
      cons' = dataCon2TyFun <$> cons
      subTys' = (\x->x{ typed = mkTyFn (typed x) }) <$> subTys
  modify (\x->x{ _bindList = cons' : _bindList x })

  pure (tyEnt ,  V.fromList rigids V.++ subTys')

--dependent -> error $ "dependent: " ++ show dependent
--          -- TyDependent argNms <$> expr2Core expr

----------
-- Data --
----------
-- ! this assumes it is the first to name anything !
getTypesAndCons :: V.Vector P.Decl -- .TypeAlias
  -> ToCoreEnv (V.Vector Binding, V.Vector Entity)
 = \datas ->
  -- type/data names may be used out of order/recursively
  -- note. convTy converts all P.TyName to TyAlias
  let registerData iNm (P.TypeAlias qNm ty)
        = addTyHName (pName2Text qNm) iNm
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
   _convData dataINm (pName2Text aliasName) ty

_convData :: IName -> HName -> P.Type
         -> ToCoreEnv (V.Vector Binding, Entity, V.Vector Entity)
 = \dataINm dataNm ty ->
  let 
      -- Functions for converting data/record
      mkSubTypes :: HName -> Int -> [HName] -> [[Type]]
                 -> ToCoreEnv ([Type], [Entity], Entity)
      mkSubTypes qual nAlts conHNames conTys = do
        let subTyHNames      = (qual `T.append`) <$> conHNames
        subTyINames <- freshTyNames nAlts
        zipWithM addTyHName subTyHNames subTyINames
        let mkSubTy i conIdx = TyMono (MonoSubTy i dataINm conIdx)
            subTypes         = zipWith mkSubTy subTyINames [0..]
            mkSubEnts hNm ty = Entity (Just hNm) ty
            subEnts          = zipWith mkSubEnts subTyHNames subTypes
        let dataDef      = DataDef dataNm (zip conHNames conTys)
            dataPolyType = PolyData (PolyUnion subTypes) dataDef
            dataEnt      = Entity (Just dataNm) (TyPoly dataPolyType)
        pure (subTypes, subEnts, dataEnt)

      mkConstructors conHNames conTys subTypes = 
        let mkCon prodNm [] subTy = LCon $ Entity (Just prodNm) subTy
            mkCon prodNm prodTy subTy =
              LCon $ Entity (Just prodNm) (TyArrow $ prodTy ++ [subTy])
        in V.fromList $ zipWith3 mkCon conHNames conTys subTypes

  in case ty of
  P.TyRecord recordAlts -> do
    let nAlts = length recordAlts
        convAlt (prodNm , (P.RecordFields fields)) = do
          let (nms, tys) = unzip fields
          (pName2Text prodNm , pName2Text<$>nms ,) <$> mapM convTyM tys
        convAlt (prodNm , (P.RecordTuple tys)) =
          (pName2Text prodNm , [] ,) <$> mapM convTyM tys
    (conHNames, fieldNames, conTys) <- unzip3 <$> mapM convAlt recordAlts

    zipWithM addHName conHNames =<< freshNames nAlts
    let qual = dataNm `T.snoc` '.'
    (subTypes, subEnts, dataEnt) <-
      mkSubTypes qual nAlts conHNames conTys

    -- record field accessor functions
    let emitAccessors :: Type-> [HName] -> [Type] -> ToCoreEnv ()
         = \subTy a b-> sequence_$zipWith3 (oneAccessor subTy) [0..] a b
        oneAccessor subTy i hNm ty = do
          argINm <- freshName
          addLocal argINm (LArg $ Entity Nothing subTy)
          accessorINm <- freshName
          let entity = Entity (Just hNm) (TyArrow [subTy, ty])
              e = App (Instr (MemInstr ExtractVal)) [Lit $ Int i]
              bind = LBind entity [argINm] e
          addHName hNm accessorINm
          addLocal accessorINm bind
    sequence_ $ zipWith3 emitAccessors subTypes fieldNames conTys

    let cons = mkConstructors conHNames conTys subTypes
    pure (cons, dataEnt, V.fromList subEnts)

  -- simple alias
  t -> convTyM t >>= \ty -> pure
      (V.empty, Entity (Just dataNm) ty, V.empty)

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

pats2Bind :: [P.Pat] -> P.PExp -> Maybe HName -> Type
          -> ToCoreEnv Binding
pats2Bind pats rhsE fNm fnSig = do
  -- special case for scopedtypevars: lift typed expr to fn sig
  (ty, pExp) <- case (fnSig, rhsE) of
      (TyUnknown, P.Typed t e) -> (,e) <$> convTyM t
      _ -> pure (fnSig, rhsE)
--let (ty , pExp) = (fnSig , rhsE)

  iNames <- freshNames (length pats)
  zipWithM mkLArg iNames pats
  expr   <- expr2Core $ pExp
  pure $ LBind (Entity fNm ty) iNames expr

-- Note. all patterns are given 1 (!) name corresponding to the
-- function argument. Bind fresh gep instructions if it's an aggregate.
mkLArg :: IName -> P.Pat -> ToCoreEnv IName = \argINm -> \case
  P.PVar hNm -> let h = pName2Text hNm
    in do -- we can sometimes give a type, but it may be wrong.
       addHName h argINm
       addLocal argINm (LArg $ Entity (Just h) TyUnknown)
  P.PTuple pNms ->
    let hNms = (\(P.PVar h) -> pName2Text h) <$> pNms
        deconTuple :: IName -> HName -> Int -> ToCoreEnv IName
        deconTuple tupleINm hNm idx  = do
          let instr = Instr $ MemInstr ExtractVal
              entity = Entity (Just hNm) TyUnknown
              expr = App instr [Lit (Int $ fromIntegral idx) , Var tupleINm]
          elemNm <- freshName
          addHName hNm elemNm
          addLocal elemNm (Inline entity expr)
    in do
      addLocal argINm (LArg $ Entity Nothing TyUnknown)
      zipWithM (deconTuple argINm) hNms [0..]
      pure argINm
  p -> error ("unknown pattern: " ++ show p)

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

------------------------
-- Functions on Names -- 
------------------------
-- Fresh
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

-- AddNames
addHName    :: T.Text -> IName -> ToCoreEnv () = \hNm nm ->
  modify (\x->x{hNames = HM.insert hNm nm (hNames x)})
addTyHName  :: T.Text -> IName -> ToCoreEnv () = \hNm nm ->
  modify (\x->x{hTyNames = HM.insert hNm nm (hTyNames x)})
rmHName    :: T.Text -> ToCoreEnv () = \hNm ->
  modify (\x->x{hNames = HM.delete hNm (hNames x)})
rmTyHName  :: T.Text -> ToCoreEnv () = \hNm ->
  modify (\x->x{hTyNames = HM.delete hNm (hTyNames x)})

getHName, getTyHName :: HName -> ToCoreEnv (Maybe IName)
getHName   hNm = gets hNames   <&> (hNm `HM.lookup`)
getTyHName hNm = gets hTyNames <&> (hNm `HM.lookup`)
mkFindHName, mkFindTyHName :: ToCoreEnv (HName -> Maybe IName)
mkFindHName   = gets hNames   <&> flip HM.lookup
mkFindTyHName = gets hTyNames <&> flip HM.lookup

lookupName   = lookupHNm . pName2Text
lookupTyName = lookupTyHNm . pName2Text
-- !!! lookups have an important additional function of bringing in
-- relevant bindings from imported modules to current modules
lookupHNm, lookupTyHNm :: HName -> ToCoreEnv (Maybe IName)
lookupHNm hNm = getHName hNm >>= \case
  Nothing -> 
    gets ({-openImports .-} imports) <&> asum . (lookupNm_Module hNm <$>)
    >>= \case
      Nothing  -> pure Nothing
      Just (iNm, cm) -> error "_"
--      let bind = bindings cm V.! iNm
--      in  Just <$> do
--        nm <- freshName
--        addHName hNm nm
--        traceM $ "adding name: " ++ show hNm
--        addLocal nm bind
--        error "untested support for external bindings"
  just -> pure just

lookupTyHNm hNm = getTyHName hNm >>= \case
  Nothing ->
    gets ({-openImports .-} imports) <&> asum . (lookupNm_Module hNm <$>)
    >>= \case
      Nothing  -> pure Nothing
      Just (iNm, cm) -> error "_"
--      let bind = algData cm V.! iNm
--      in  Just <$> do 
--        nm <- freshTyName
--        addTyHName hNm nm
--        traceM "adding tyname"
--        addLocalTy nm bind
--        error "untested support for external bindings"
  just -> pure just

lookupNm_Module :: HName->CoreModule -> Maybe (IName, CoreModule)
lookupNm_Module   nm cm = (,cm) <$> nm `HM.lookup` hNameBinds cm
lookupTyNm_Module :: HName->CoreModule -> Maybe (IName, CoreModule)
lookupTyNm_Module nm cm = (,cm) <$> nm `HM.lookup` hNameTypes cm

addLocalTy  :: IName -> Entity -> ToCoreEnv IName =
 \iNm ty -> do
--  modify (\x->x{localTys=(localTys x `V.snoc` ty)})
  tys <- gets _tyList
  let h : end = tys
      h' = h `V.snoc` ty
      tys' = h' : end
  modify (\x->x{_tyList = tys'})
  pure iNm
addLocal    :: IName -> Binding -> ToCoreEnv IName =
  \iNm bind -> do
--  modify (\x->x{localBinds=V.snoc (localBinds x) bind })
  modify (\x->x{localBinds= localBinds x `V.snoc` bind })
  pure iNm

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

------------------------
-- Main conv function --
------------------------
parseTree2Core :: [CoreModule] -> P.Module -> CoreModule
parseTree2Core topImports = let
  emptyConvState = ConvState
    { imports        = V.fromList topImports --Imports { openImports = topImports , qualImports = HM.empty }
    , localFixities  = HM.empty
    , nameCount      = 0
    , tyNameCount    = 0
    , hNames         = HM.empty
    , hTyNames       = HM.empty

    , _tyList        = []
    , _bindList      = []
    , localBinds     = V.empty
--  , localTys       = V.empty
    , localModules   = []
    , toCoreErrors   = noErrors
    }
  in _parseTree2Core emptyConvState topImports

-- having control over the start state is useful for let-bindings
-- that are passed through _parseTree2Core
-- then need to be appended to the parent module without conflicts
_parseTree2Core :: ConvState -> [CoreModule] -> P.Module -> CoreModule
_parseTree2Core startConvState topImports (P.Module mName parseTree)
 = CoreModule
  { moduleName     = pName2Text mName
  , algData        = dataTys
  , bindings       = binds
  , classDecls     = classDecls'
  , defaults       = IM.empty
  , fixities       = localFixities endState
  , tyConInstances = V.empty
  , hNameBinds     = hNames   endState
  , hNameTypes     = hTyNames endState
  }
  where
  (binds, dataTys, classDecls') = val
  (val, endState) = runState toCoreM startConvState

  -- Add a module to the ToCoreEnv state
  -- !! it is critical that the module doesn't reference itself,
  -- since those indexes are invalid in the new module
  -- It should primarily contain extern decls
  addModule :: CoreModule -> ToCoreEnv () = \cm ->
    modify (\x->x
      { _bindList = bindings cm : _bindList x
      , _tyList   = algData  cm : _tyList x
      , nameCount   = nameCount x   + V.length (bindings cm)
      , tyNameCount = tyNameCount x + V.length (algData cm)
      -- union is left-biased
      , hNames   = hNames   x `HM.union` hNameBinds cm
      , hTyNames = hTyNames x `HM.union` hNameTypes cm
      -- TODO check no overwrites
      , localFixities = localFixities x `HM.union` fixities cm
  --  , defaults = defaults x `IM.union` defaults cm
      })

  -- Note. types and binds vectors must match iNames
  -- topBindings;typeDecls;localBindings;overloads;externs
  toCoreM :: ToCoreEnv (BindMap, TypeMap, V.Vector ClassDecl) = do
    -- 0. set up imported modules
    case topImports of
      []   -> pure ()
      [cm] -> addModule cm -- modify(\x->x{imports=cm : imports x})-- addModule cm
      _    -> error "multiple modules unsupported"

    -- 1. register fixity declarations
    modify (\x->x{localFixities=convFixities (P.fixities parseTree)})

    -- 2. data: get the constructors and dataEntities (name + dataty)
    (cons, dataEntities) <- getTypesAndCons (P.tyAliases parseTree)
    modify (\x->x{ _bindList = cons         : _bindList x
                 , _tyList   = dataEntities : _tyList x })

    -- 3. extern entities
    externs <- mapM (doExtern dataEntities) (P.externs parseTree)
    modify (\x->x{_bindList = (LExtern <$> externs) : _bindList x})

    -- 4. type functions:
    tyFunINms<- V.fromList<$>freshTyNames (V.length (P.tyFuns parseTree))
    (typeFuns, datas) <- V.unzip <$> V.zipWithM doTypeFun (P.tyFuns parseTree) tyFunINms
    let datas' = V.foldl' (V.++) V.empty datas
    modify (\x->x{ _tyList = datas' : typeFuns : _tyList x })

    -- 5. typeclasses
    -- note. classDecls includes local bindings (they must match iNames)
    (classDecls, topClassFns)
      <- doTypeClasses (P.classes parseTree) (P.classInsts parseTree)
    -- also take + clear locals from overloads + default functions
    modify (\x->x{ _bindList  = localBinds x : topClassFns : _bindList x
                 , localBinds = V.empty
                 })

    -- 6. expression bindings
    (hNSigMap :: M.Map HName Type) <- mkSigMap (P.topSigs parseTree)
    let findTopSig :: HName -> Maybe Type = \hNm -> M.lookup hNm hNSigMap
    fnBinds  <- getFns findTopSig (P.topBinds parseTree)
    fnLocals <- gets localBinds
    modify (\x->x{_bindList = fnLocals : fnBinds : _bindList x })

    -- 7. Collect results
    -- ! the resulting vectors must be consistent with all iNames !
    binds      <- V.concat . reverse <$> gets _bindList
    tyEntities <- V.concat . reverse <$> gets _tyList
    pure (binds, tyEntities, classDecls)

-- TODO remove
partitionFns = partition $ \case { P.TypeSigDecl{}->True ; _-> False }

-------------
-- Classes --
-------------
doClassDecl :: P.Decl -> ToCoreEnv (ClassDecl , V.Vector Entity)
doClassDecl (P.TypeClass classNm classVarPNames decls) =
  let
    classVars = pName2Text <$> V.fromList classVarPNames
    (sigs, defaultBinds) = partitionFns decls

    registerClassFns sigs =
      let registerFn (P.TypeSigDecl nms sig) =
            mapM (\h -> addHName (pName2Text h) =<< freshName) nms
      in  mapM registerFn sigs

    sig2ClassFn :: V.Vector IName -> P.Decl{-.TypeSigDecl-}
                -> ToCoreEnv (ClassFn , V.Vector Entity)
    sig2ClassFn iclassVars (P.TypeSigDecl [nm] sig) = do -- TODO [nm]
      let mkEntity ty nm = Entity (Just (pName2Text nm)) ty
      (sigEnt , rigids) <- doTyFun (pName2Text nm) (-1) classVars sig
      let sigTy = typed sigEnt
          classFn = ClassFn {
            classFnInfo = mkEntity sigTy nm
          , defaultFn   = Nothing }
      pure (classFn , rigids)
  in do
    let classArity = length classVars
    registerClassFns sigs

    -- convert classFns with classArgs locally available in HNameMap
    classArgs <- V.fromList <$> (freshNames classArity)
    V.zipWithM addTyHName classVars classArgs
    (classFnEntities , rigids)<-unzip<$>mapM (sig2ClassFn classArgs) sigs
    V.mapM rmTyHName classVars

    let classDecl = ClassDecl
          { className = pName2Text classNm
          , classVars = classVars
          , classFns  = V.fromList classFnEntities }
    pure (classDecl , V.concat rigids)

doTypeClasses :: V.Vector P.Decl -> V.Vector P.Decl
 -> ToCoreEnv (  V.Vector ClassDecl -- exported classDecl info
               , V.Vector Binding)  -- class tycons (top bindings)
doTypeClasses p_TyClasses p_classInsts = do
  (classDecls , rigids) <- V.unzip <$> V.mapM doClassDecl p_TyClasses

  let classNms = className <$> classDecls
      declMap  = HM.fromList $ V.toList $ V.zip classNms classDecls
      doInstance inst@(P.TypeClassInst instNm _ _) =
        let classDecl = case HM.lookup (pName2Text instNm) declMap of
              Just h -> h
              Nothing -> error ("class not in scope: " ++ show instNm)
        in doClassInstance inst classDecl
  perInstOverloads <- V.mapM doInstance p_classInsts
  let (instVars , class2OverloadMaps) = V.unzip perInstOverloads
      vconcat = V.foldl' (V.++) V.empty
      classFns' = vconcat $ classFns <$> classDecls
      classEnts = classFnInfo <$> classFns'
      overloadMaps = V.zipWith mkMap instVars class2OverloadMaps
      mps = V.fromList $ transpose $ V.toList overloadMaps
      classFs = V.zipWith LClass classEnts (M.fromList <$> mps)

  modify (\x->x{ _tyList = vconcat rigids : _tyList x })
  pure (classDecls , classFs)

mkMap :: [Type] -> IM.IntMap IName -> [([Type], IName)]
mkMap instTys classFn2OverloadMap =
  (instTys , ) <$> (IM.elems classFn2OverloadMap)

doClassInstance :: P.Decl{-.TypeClassInst-} -> ClassDecl
  -> ToCoreEnv ([Type] , IM.IntMap IName) -- ClassINm -> INm
 -- tycon args , classINms, overloadINms
 = \(P.TypeClassInst instNm [instTyNm] decls)
    (ClassDecl classNm classVars classFns) ->
  let instTyHNm = pName2Text instTyNm
      (sigs, fnBinds) = partitionFns decls
      genOverload (P.FunBind [(P.Match fName pats rhs)]) =
        let fHName = pName2Text fName
            scopedName = P.Ident $ fHName `T.append` T.cons '.' instTyHNm
            match' = P.Match scopedName pats rhs
        in do
         classFnNm <- lookupHNm fHName <&> \case
           Nothing -> error $ "unknown class function: " ++ show fName
           Just i  -> i
         (classFnNm , ) <$> match2LBind match' TyUnknown
  in do
    -- TODO check the instances respect classFnSigs
    -- TODO minimum instance definition ?
    sigMap <- mkSigMap (V.fromList sigs)
    let findInstSig hNm = M.lookup hNm sigMap

    instTy <- lookupTyHNm instTyHNm <&> \case
      { Just i -> TyAlias i ; Nothing -> error "unknown type" }

    startOverloadId <- gets nameCount
    (classFnINms, overloadBinds) <- unzip <$> mapM genOverload fnBinds
    let nOverloads = length overloadBinds
        overloadINms = take nOverloads [startOverloadId-1..]
    modify (\x->x{ nameCount = nameCount x + nOverloads })
    zipWithM addLocal overloadINms overloadBinds
    pure $ ([instTy] , IM.fromList (zip classFnINms overloadINms))

expr2Core :: P.PExp -> ToCoreEnv CoreExpr = \case
  P.Var (P.UnQual hNm) -> lookupName hNm >>= \case
    Just n  -> pure $ Var n
    Nothing -> lookupTyName hNm >>= \case
      Just tyN -> pure $ TypeExpr (TyAlias tyN)
      Nothing  -> error ("expr2Core: not in scope: " ++ show hNm)
  P.Con pNm           -> expr2Core (P.Var pNm) -- same as Var
  P.Lit l             -> do
    iNm <- freshName
    let classNm = case l of
          Char   c -> "Num"
          Int    i -> "Int"
          Frac   r -> "Float"
          String s -> "CharPtr"
          Array lits -> "CharPtr"
    maybeTy  <- lookupTyHNm $ T.pack $ classNm
    let ty = case maybeTy of
          Nothing -> error ("Internal: prim typeclass not in scope: "
                            ++ show classNm)
          Just t  -> TyAlias t
--  addLocal iNm (LBind (Entity Nothing ty) [] (Lit l))
    addLocal iNm (LLit (Entity Nothing ty) l)
    pure $ Var iNm

  P.PrimOp primInstr  -> pure $ Instr primInstr
--P.Infix nm          -> expr2Core (P.Var nm)
  -- we cannot produce structs/data for tuples
  -- if we don't know the types yet !
  P.App f args        ->
    let handlePrecedence f args
          = App <$> expr2Core f <*> mapM expr2Core args
    in handlePrecedence f args

  P.InfixTrain leftExpr infixTrain -> 
    gets localFixities >>= \fixities ->
    let
    getFixity x = case pQName2Text x `HM.lookup` fixities of
      Just  f -> f
      Nothing -> defaultFixity
    lOp `hasPrec`rOp =
      let Fixity precL assocL = getFixity lOp
          Fixity precR assocR = getFixity rOp
      in case compare precR precL of
          GT -> True
          EQ -> assocL == LAssoc
          LT -> False
    -- General plan is to fold handlePrec over the infixTrain
    -- 1. if rOp has higher prec then lOp then add it to the opStack
    -- 2. else apply infixes from opStack until stack has lower prec then rOp
    -- 3. finally Apply everything remaining in the _opStack
    handlePrec :: (P.PExp, [(P.QName, P.PExp)]) -> (P.QName, P.PExp)
               -> (P.PExp, [(P.QName, P.PExp)])
    handlePrec (expr, []) (rOp, rExp) = (P.App (P.Var rOp) [expr, rExp] , [])
    handlePrec (expr, (lOp, lExp) : stack) next@(rOp, _) =
      if lOp `hasPrec` rOp -- getInfix rOp > getInfix lOp
      then (expr , next : (lOp, lExp) : stack)
      else handlePrec (P.App (P.Var lOp) [expr, lExp] , stack) next
    (expr', remOpStack) = foldl' handlePrec (leftExpr, []) infixTrain
    -- apply all ops remaining in opStack
    expr = let infix2App lExp (op, rExp) = P.App (P.Var op) [lExp, rExp]
           in foldl' infix2App expr' remOpStack
    in expr2Core $ expr

  P.Let (P.BDecls binds) exp -> _
--  gets imports >>= \topImports ->
--  let letModule      = P.Module (P.Ident $ T.pack "_Let") binds
--      topOpenImports = openImports topImports
--      letMod         = parseTree2Core topOpenImports letModule
--  in do
--  modify (\x->x{imports=(imports x){openImports=letMod : openImports (imports x)}})
--  modify (\x->x{localTys=  (localTys x) V.++ algData letMod})
    expr2Core exp

  -- lambdas are Cases with 1 alt
  -- TODO similar to match2Lbind !
  --match2LBind :: P.Match -> Type -> ToCoreEnv Binding = \m fnSig ->
  P.Lambda pats f   -> mdo
      fIName <- freshName
      addLocal fIName bind -- need to add this before new freshNames
      bind <- pats2Bind pats f (Nothing) TyUnknown
      pure $ Var fIName

  P.LambdaCase alts -> do
      fIName <- freshName
      iArg   <- freshName
      expr   <- getCaseAlts alts (Var iArg)
      let bind = LBind (Entity Nothing TyUnknown) [iArg] expr
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
          pure $ Case ifE' $ Switch [(lTrue, thenE'), elseAlt]
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
    (ty , expr) <- -- CU.localState $
      (,) <$> convTyM t <*> expr2Core e
    addLocal iNm (LBind (Entity Nothing ty) [] expr)
    pure $ Var iNm
  other -> error $ show other
--P.SectionL
--P.SectionR
--other -> error ("strange expr: " ++ show other)

-- getCaseAlts returns a partial constructor for a CoreExpr
-- biggest point is to accomodate both P.Case and P.LambdaCase cleanly
-- There are many patterns to handle here, and it is often necessary
-- to chain case expressions
getCaseAlts :: [P.Alt] -> CoreExpr -> ToCoreEnv CoreExpr
 = \alts e ->
  -- dataCase: all alts have type (Name [Name] expr)
  -- then it's a data decomposition
  let 
  -- Rearrange infixes into normal form
  doInfixPats :: P.Pat -> P.Pat = \case
    P.PInfixApp p1 n ps ->
      let a = doInfixPats p1
          b = doInfixPats ps
      in doInfixPats $ P.PApp n (p1:[ps])
    P.PApp qNm ps -> P.PApp qNm (doInfixPats <$> ps)
    other -> other

  varOrNothing = \case { P.PVar n->Just (pName2Text n) ; _->Nothing }

  convAlt :: P.Alt -> ToCoreEnv (Maybe (IName, [IName], CoreExpr))
  convAlt (P.Alt pat (P.UnGuardedRhs pexp))
   = case doInfixPats pat of
    P.PVar hNm -> lookupName hNm >>= \case
       Nothing -> error ("unknown name in pattern: " ++ show hNm)
       Just n -> expr2Core pexp >>= \exp ->
            pure $ Just (n, [], exp)
    P.PApp hNm argPats -> lookupHNm (pQName2Text hNm) >>= \case
       Nothing -> error ("unknown Constructor:" ++ show hNm)
       Just n  ->
         -- check they're all Just
         let args = case sequence (varOrNothing <$> argPats) of
                      Just x -> x
                      Nothing -> error "failed to convert pattern"
         in do
         iArgs <- freshNames (length args) -- mapM (\_ -> freshName) args
         zipWithM (\i hNm -> (addHName hNm i)
                   *> addLocal i (LArg (Entity (Just hNm) TyUnknown)))
                  iArgs args
         exp <- expr2Core pexp
         pure $ Just (n, iArgs, exp)
    P.PTuple args -> error "tuple in case"
    _ -> pure Nothing
--  P.PLit l -> _
--  P.PTuple p -> _
--  P.PList ps -> _
--  P.PWildCard -> _
  in do
  dataCase <- sequence <$> mapM convAlt alts
  -- switchCase: all alts must be literals
  let litAlts = _ -- no switchCase for now
  -- TODO Switch case
  pure $ case dataCase of
    Just alts -> Case e (Decon alts)
    Nothing   -> Case e (Switch litAlts)

-- fixities
defaultPrec = 9
defaultFixity = Fixity defaultPrec LAssoc

convFixities :: V.Vector P.Decl{- .InfixDecl-} -> HM.HashMap HName Fixity
convFixities decls = 
  let convAssoc = \case
        P.AssocRight -> RAssoc
        P.AssocNone  -> LAssoc
        P.AssocLeft  -> LAssoc
      convFixity = \case { Just i -> i ; Nothing -> defaultPrec }
      infix2pair (P.InfixDecl a f [op])
        = (pName2Text op , Fixity (convFixity f) (convAssoc a))
  in HM.fromList $ V.toList $ infix2pair <$> decls
