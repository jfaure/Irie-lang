-- ParseTree -> Core

-- 1. construct vectors for bindings, types and classes
-- 2. resolve infix apps (including precedence)
-- 3. convert all HNames to INames (indexes into vectors)
-- 4. desugar language expressions
module ToCore (parseTree2Core)
where

import Prim
import CoreSyn
import Names
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
import Control.Applicative
import Data.Functor
import Data.Foldable
import GHC.Exts (groupWith)
import Debug.Trace

transpose []             = []
transpose ([]    : xss)  = transpose xss
transpose ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])

------------
-- ConvTy --
------------
data ConvTyError
 = UnknownTy    HName
 | UnknownTyVar HName
 | UnexpectedTy P.Type
 deriving (Show)

-- Error handling is different if the ty is in a type function
convTy :: (HName -> Maybe IName) -> P.Type -> Either ConvTyError Type
 = \findNm ->
 let convTy' = convTy findNm
 in \case
  P.TyPrim t               -> Right$TyMono$MonoTyPrim t
  P.TyPoly (P.PolyAnd   f) -> TyPoly . PolyMeet <$> mapM convTy' f
  P.TyPoly (P.PolyUnion f) -> TyPoly . PolyJoin     <$> mapM convTy' f
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
-- TODO cancer
convTyM :: P.Type -> ToCoreEnv Type = \pTy ->
  mkFindTyHName <&> (`convTy` pTy) >>= \case
  Right ty -> pure ty
  Left  er -> let
   addTys pTy ty = do 
    lookupTyHNm ty >>= \case
      Just i -> convTyM pTy
      Nothing -> do
    -- register implicit forall tynames
        nm <- freshTyName
        addTyHName ty nm
        addLocalTy nm $ CU.mkAnonEntity (TyRigid nm)
        convTyM pTy
   in case er of
    UnknownTy ty    -> --error ("unknown typeName: " ++ show ty)
      addTys pTy ty
    UnknownTyVar ty -> --error ("unknown typeName: " ++ show ty)
      addTys pTy ty
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
      rigids   = (\ty -> CU.mkAnonEntity ty) <$> rigidTys

  V.zipWithM addTyHName argHNms (V.fromList argNms)
  rhs <- (`convTy` ty) <$> mkFindTyHName
  (fnBody , cons , subTys) <- case rhs of
    Right t -> pure (t , V.empty , V.empty)
    Left (UnexpectedTy dataDef@(P.TyRecord alts)) -> do
      -- handle TyCons returning data
      (cons, dTy, subTys) <- _convData tyFunINm tyFnHNm dataDef
      pure $ (typed dTy , cons , subTys)
    Left t -> error $ "unexpected return type of tyFunction: " ++ show t
  mapM rmTyHName argHNms

  let tyFn  = TyFn argNms fnBody
      tyEnt = CU.mkNamedEntity tyFnHNm tyFn

  -- if TyFun returns data, wrap it's constructor types
  let mkTyFn ty = TyFn argNms ty
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
          subTypes = zipWith mkSubTy subTyINames [0..]
          subEnts  = zipWith CU.mkNamedEntity subTyHNames subTypes
      let dataDef      = DataDef dataNm (zip conHNames conTys)
          dataPolyType = PolyData (PolyJoin subTypes) dataDef
          dataEnt      = CU.mkNamedEntity dataNm (TyPoly dataPolyType)
      pure (subTypes, subEnts, dataEnt)

    mkConstructors conHNames conTys subTypes = 
      let mkCon prodNm [] subTy = LCon $ CU.mkNamedEntity prodNm subTy
          mkCon prodNm prodTy subTy =
            LCon $ CU.mkNamedEntity prodNm (TyArrow $ prodTy ++ [subTy])
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
         = \subTy a b-> sequence_
            $ zipWith3 (oneAccessor subTy) [0..] a b
        oneAccessor subTy i hNm ty = do
          argINm <- freshName
          addLocal argINm (LArg (CU.mkAnonEntity subTy) 0)
          accessorINm <- freshName
          let ent = CU.mkNamedEntity hNm (TyArrow [subTy, ty])
              e = Instr (MemInstr ExtractVal) [Lit $ Int i]
              bind = LBind ent [argINm] e
          addHName hNm accessorINm
          addLocal accessorINm bind
    sequence_ $ zipWith3 emitAccessors subTypes fieldNames conTys

    let cons = mkConstructors conHNames conTys subTypes
    pure (cons, dataEnt, V.fromList subEnts)

  -- simple alias
  t -> convTyM t <&> \ty ->
      (V.empty, CU.mkNamedEntity dataNm ty, V.empty)

-- getFns: generate bindings from a [P.Decl]
-- both normal fns and typeclass funs use this
getFns :: (HName->Maybe Type) -> V.Vector P.Decl -> ToCoreEnv (V.Vector Binding, Int)
getFns findSig fnBindings = let
  registerBinds :: (HName->Maybe Type) -> P.Decl
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
  nTopBinds <- gets nameCount
  (, nTopBinds) <$> V.zipWithM match2LBind matches tys

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
  hNms <- zipWithM mkLArg iNames pats
  case pExp of
    P.PrimOp instr -> pure $ LInstr (CU.mkEntity fNm ty) instr
    _ -> LBind (CU.mkEntity fNm ty) iNames <$> expr2Core pExp
--traverse (maybe (pure ()) rmHName) hNms

-- Note. all patterns are given 1 (!) name corresponding to the
-- function argument. Bind fresh gep instructions if it's an aggregate.
mkLArg :: IName -> P.Pat -> ToCoreEnv (Maybe HName)
 = \argINm -> \case
  P.PVar hNm -> let h = pName2Text hNm
    in do -- we can sometimes give a type, but it may be wrong.
       addHName h argINm
       addLocal argINm $ LArg (CU.mkNamedEntity h TyUnknown) 0
       pure (Just h)
  P.PTuple pNms -> deconTuple argINm pNms *> pure Nothing
  p -> error ("unknown pattern: " ++ show p)

deconTuple :: IName -> [P.Pat] -> ToCoreEnv IName
deconTuple argINm pNms =
  let hNms = (\(P.PVar h) -> pName2Text h) <$> pNms
      deconTupleArg :: IName -> HName -> Int -> ToCoreEnv IName
      deconTupleArg tupleINm hNm idx  = do
        let instr = Instr $ MemInstr ExtractVal
            entity = CU.mkNamedEntity hNm TyUnknown
            expr = instr [Lit (Int $ fromIntegral idx) , Var tupleINm]
        elemNm <- freshName
        addHName hNm elemNm
        addLocal elemNm (Inline entity expr)
  in do
    addLocal argINm $ LArg (CU.mkAnonEntity TyUnknown) 0
    zipWithM (deconTupleArg argINm) hNms [0..]
    pure argINm

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
    pure $ CU.mkNamedEntity hNm externTy
  in \case
    P.Extern   nm ty -> addExtern PrimExtern   nm ty
    P.ExternVA nm ty -> addExtern PrimExternVA nm ty

------------------------
-- Main conv function --
------------------------
parseTree2Core :: V.Vector CoreModule -> P.Module -> CoreModule
parseTree2Core topImports = _parseTree2Core st topImports
 where st = emptyConvState { imports = topImports }

emptyConvState = ConvState
  { imports        = V.empty --Imports { openImports = topImports , qualImports = HM.empty }
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

-- having control over the start state is useful for let-bindings
-- that are passed through _parseTree2Core
-- then need to be appended to the parent module without conflicts
_parseTree2Core :: ConvState -> V.Vector CoreModule -> P.Module
  -> CoreModule
_parseTree2Core startConvState topImports (P.Module mName parseTree)
 = CoreModule
  { moduleName     = pName2Text mName
  , algData        = dataTys
  , bindings       = binds
  , nTopBinds      = nTopBinds'
  , classDecls     = classDecls'
  , defaults       = IM.empty
  , fixities       = localFixities endState
  , tyConInstances = V.empty
  , hNameBinds     = hNames   endState
  , hNameTypes     = hTyNames endState
  }
  where
  (binds, nTopBinds' , dataTys, classDecls') = val
  (val, endState) = runState toCoreM startConvState

  toCoreM :: ToCoreEnv (BindMap, Int , TypeMap, V.Vector ClassDecl) = do
  -- Note. types and binds vectors must match iNames
  -- topBindings;typeDecls;localBindings;overloads;externs

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
    (fnBinds , nTopBinds)  <- getFns findTopSig (P.topBinds parseTree)
    fnLocals <- gets localBinds
    modify (\x->x{_bindList = fnLocals : fnBinds : _bindList x })

    -- 7. Collect results
    -- ! the resulting vectors must be consistent with all iNames !
    binds      <- V.concat . reverse <$> gets _bindList
    tyEntities <- V.concat . reverse <$> gets _tyList
    pure (binds, nTopBinds , tyEntities, classDecls)

-- TODO remove
partitionFns = partition $ \case { P.TypeSigDecl{}->True ; _-> False }

-------------
-- Classes --
-------------
-- * ClassDecl: a description of the interface that must be satisfied by instances
--   ie. function signatures, defaults and superclasses
-- * classFn: a jointyped function shared by all instances.
--   includes a map InstanceType->InstanceId for instantiation purposes (in typejudge)
doClassDecl :: P.Decl -> ToCoreEnv ClassDecl
doClassDecl (P.TypeClass classNm [] supers decls) =
  let
    (sigs, defaultBinds) = partitionFns decls
    registerClassFns sigs =
      let registerFn (P.TypeSigDecl nms sig) =
            mapM (\h -> addHName (pName2Text h) =<< freshName) nms
      in  mapM registerFn sigs
    sig2ClassFn (P.TypeSigDecl [nm] sig) = do
      sigTy <- convTyM sig
      pure $ ClassFn {
        classFnInfo = CU.mkNamedEntity (pName2Text nm) sigTy
      , defaultFn   = Nothing }
  in do
    registerClassFns sigs
    classFnEntities <- mapM sig2ClassFn sigs
    pure $ ClassDecl
      { className = pName2Text classNm
      , classFns  = V.fromList classFnEntities
      , supers    = pName2Text <$> supers }

doTypeClasses :: V.Vector P.Decl -> V.Vector P.Decl
 -> ToCoreEnv (  V.Vector ClassDecl -- exported classDecl info
               , V.Vector Binding)  -- class tycons (top bindings)
doTypeClasses p_TyClasses p_classInsts = do
  classDecls <- V.mapM doClassDecl p_TyClasses
  let classNms = className <$> classDecls
      declMap  = HM.fromList $ V.toList $ V.zip classNms classDecls
      doInstance inst@(P.TypeClassInst instNm _ _) =
        let classDecl = case HM.lookup (pName2Text instNm) declMap of
              Just h -> h
              Nothing -> error ("class not in scope: " ++ show instNm)
        in doClassInstance inst classDecl
  perInstOverloads <- V.mapM doInstance p_classInsts

  -- class2Overmaps : foreach ClassNm ; [classFn]
  -- mps = foreach classFn; ITName --> instFn
  let (instVars , supers , class2OverloadMaps)= V.unzip3 perInstOverloads
      vconcat = V.foldl' (V.++) V.empty
      -- mkmap : use instTys rather than classTys in the map
      mkMap :: ITName -> ITMap IName -> [(ITName, IName)]
      mkMap instTys classFn2OverloadMap =
        (instTys , ) <$> (IM.elems classFn2OverloadMap)
      overloadMaps = V.zipWith mkMap instVars class2OverloadMaps
      mps = V.fromList $ transpose $ V.toList overloadMaps

      mkLClasses classDecl overloadMap = let
        mkLCls clsInf = LClass clsInf (className classDecl) overloadMap
        in mkLCls <$> (classFnInfo <$> classFns classDecl)
      classFs = V.zipWith mkLClasses classDecls $ M.fromList <$> mps

  genPolyTypes instVars supers -- produce join type for each class

  pure (classDecls , vconcat classFs)

-- produce union types for each class polytype, eg:
-- Num  := BigInt u Int u Real
genPolyTypes :: V.Vector IName -> V.Vector [T.Text]
  -> ToCoreEnv [IName]
genPolyTypes instVars supers = do
  -- small complication: need to add instances to superclasses
  let addInst = \mp (instVar , supers) ->
        foldl' (\m s -> HM.insertWith (++) s [instVar] m) mp supers
      subTyMap = V.foldl' addInst HM.empty (V.zip instVars supers)
  polyNames <- freshTyNames (HM.size subTyMap)
  zipWithM addTyHName (HM.keys subTyMap) polyNames
  let addTy i (hNm,tys) =
        let ent = CU.mkNamedEntity hNm (TyPoly$PolyJoin (TyAlias <$> tys))
        in addLocalTy i ent
  zipWithM addTy polyNames (HM.toList subTyMap)

doClassInstance :: P.Decl{-.TypeClassInst-} -> ClassDecl
  -> ToCoreEnv (ITName , [HName] , ITMap IName) -- ClassINm -> INm
 -- tycon args , classINms, overloadINms
 = \(P.TypeClassInst instNm [instTyNm] decls)
    (ClassDecl classNm classFns superClasses) ->
  let instTyHNm = pName2Text instTyNm
      supers = classNm : superClasses
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

    let lookupINm hNm = lookupTyHNm hNm <&> \case
          { Just i->i ; Nothing -> error "unknown type" }
    instTy <- lookupINm instTyHNm

    (classFnINms, overloadBinds) <- unzip <$> mapM genOverload fnBinds
    startOverloadId <- gets nameCount
    let nOverloads = length overloadBinds
        overloadINms = take nOverloads [startOverloadId..]
    modify (\x->x{ nameCount = nameCount x + nOverloads })
    zipWithM addLocal overloadINms overloadBinds
    pure $ (instTy, supers, IM.fromList (zip classFnINms overloadINms))

expr2Core :: P.PExp -> ToCoreEnv CoreExpr = \case
  P.Var (P.UnQual hNm) -> lookupName hNm >>= \case
    Just n  -> pure $ Var n
    Nothing -> lookupTyName hNm >>= \case
      Just tyN -> pure $ TypeExpr (TyAlias tyN)
      Nothing  -> error ("expr2Core: not in scope: " ++ show hNm)
  P.Con pNm           -> expr2Core (P.Var pNm) -- same as Var
  P.Lit l -> pure $ case l of
    PolyInt{} ->  Instr MkNum  [Lit l]
    PolyFrac{} -> Instr MkReal [Lit l]
    _ -> Lit l -- do

  P.PrimOp primInstr ->
    let arity = 2
        ent = (CU.mkAnonEntity TyUnknown)
    in do
    i <- freshName
    addLocal i (LInstr ent primInstr)
    pure $ Var i
--  fn <- freshName
--  args <- freshNames arity
--  mapM (\i -> addLocal i (LArg ent 1)) args
--  Var <$> addLocal fn (LBind ent args (Instr primInstr (Var <$> args)))

  P.App f args -> expr2Core f >>= \case
    Var fId -> App fId <$> mapM expr2Core args
    other   -> error $ "weird fn: " ++ show other

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

  -- lambdas are Cases with 1 alt
  -- TODO similar to match2Lbind !
  --match2LBind :: P.Match -> Type -> ToCoreEnv Binding = \m fnSig ->
  P.Lambda pats f -> mdo
      fIName <- freshName
      addLocal fIName bind -- need to add this before new freshNames
      bind <- pats2Bind pats f (Nothing) TyUnknown
      pure $ Var fIName

  P.LambdaCase alts -> do
      fIName <- freshName
      iArg   <- freshName
      expr   <- getCaseAlts alts (Var iArg)
      let bind = LBind (CU.mkAnonEntity TyUnknown) [iArg] expr
      addLocal fIName bind
      pure $ Var fIName

  -- [(PExp, PExp)]
  P.MultiIf allAlts    -> let
    -- split off the last alt to allow us to fold it
    (lastIfE, lastElseE) = last allAlts
    alts = init allAlts
    (lTrue, lFalse) = (Int 1, Int 0)
    mkSwitch ifE thenE elseAlt = do
      ifE'   <- expr2Core ifE
      thenE' <- expr2Core thenE
      pure $ Case ifE' $ Switch [(lTrue, thenE'), elseAlt]
--  f :: ((PExp,PExp) -> CoreExpr.SwitchCase -> CoreExpr.SwitchCase)
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
    addLocal iNm (LBind (CU.mkAnonEntity ty) [] expr)
    pure $ Var iNm
--P.SectionL
--P.SectionR

  P.Let pTree exp -> do
    -- lets are modules, with the distinction that we still codegen them
    -- , which is why they're assigned names immediately
    tyCnt <- gets tyNameCount
    nmCnt <- gets nameCount
    let letConvState = emptyConvState {
            tyNameCount = tyCnt
          , nameCount = nmCnt }
        pMod = P.Module (P.Ident T.empty) pTree
        letMod = _parseTree2Core letConvState V.empty pMod
    loc <- gets id
    modify(\x->x{localModules=letMod : localModules x
                , nameCount   = nameCount x + V.length (bindings letMod)
                , tyNameCount = tyNameCount x + V.length (algData letMod)
                , localBinds  = localBinds x V.++ bindings letMod
                , _tyList     = algData  letMod : _tyList x
                })
    exp <- expr2Core exp
    modify(\x->x{localModules = drop 1 (localModules x)})
    pure exp

  other -> error ("unhandled expr: " ++ show other)

--incUse :: IName -> ToCoreEnv () = \n newBind ->
-- let doUpdate cm =
--      let binds = V.modify (\v->MV.write v n newBind) (bindings cm)
--      in  cm { bindings=binds }
-- in gets  modify (\x->x{ coreModule = doUpdate (coreModule x) })

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

  doLitAlt = \case
    P.PLit l -> _

  convDecon :: P.Alt -> ToCoreEnv (Maybe (IName, [IName], CoreExpr))
  convDecon (P.Alt pat (P.UnGuardedRhs pexp))
   = case doInfixPats pat of
    P.PVar nm -> lookupName nm >>= \case
      Nothing -> error ("unknown name in pattern: " ++ show nm)
      Just n -> expr2Core pexp <&> Just . (n, [], )
    P.PApp nm argPats -> lookupHNm (pQName2Text nm) >>= \case
      Nothing -> error ("unknown Constructor:" ++ show nm)
      Just n  -> let 
          varOrNothing = \case { P.PVar n->Just (pName2Text n)
                               ; _->Nothing }
          args = case traverse varOrNothing argPats of
                Just x -> x
                Nothing -> error "failed to convert pattern"
          registerLArg i hNm = addHName hNm i
            *> addLocal i (LArg (CU.mkNamedEntity hNm TyUnknown) 0)
        in do
        iArgs <- freshNames (length args)
        zipWithM registerLArg iArgs args
        Just . (n, iArgs , ) <$> expr2Core pexp
    P.PTuple args -> error "tuple in case" -- deconTuple
    P.PLit l    -> pure Nothing
    P.PList ps  -> _
    P.PWildCard -> _
  in do
  dataCase <- sequence <$> mapM convDecon alts
  pure $ case dataCase of
    Just alts -> Case e (Decon alts)
    Nothing   -> Case e $ Switch _ -- (doLitAlt <$> alts)

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
