-- ParseTree -> Core

-- 1. resolve infix apps (including precedence)
-- 2. convert all HNames to INames (indexes into vectors)
-- 3. desugar language expressions
module ToCore -- (parseTree2Core)
where
{-
import Prim
import CoreSyn
--import Names
import qualified CoreUtils as CU
import qualified ParseSyntax as P

import qualified Data.Vector         as V
import qualified Data.Text           as T
import qualified Data.Map.Strict     as M
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict  as IM
import Control.Monad.Trans.State.Strict
import Data.List (partition, sortOn)
import Data.Foldable (foldrM)
import Control.Monad (zipWithM)
import Control.Applicative
import Data.Functor
import Data.Foldable
import GHC.Exts (groupWith)
import Debug.Trace

convTy :: (HName -> Maybe IName) -> P.Type -> TyPlus
 = \findHNm -> \case
 _ -> []

-- Default behavior for top level type signatures,
-- new variables are implicitly quantified
convTyM :: P.Type -> ToCoreEnv TyPlus = \pTy -> mkFindTyHName <&> (`convTy` pTy)

--pats2Bind :: [P.Pat] -> P.TT -> Maybe HName -> Type
--          -> ToCoreEnv Binding
--pats2Bind pats rhsE fNm fnSig = do
--  -- special case for scopedtypevars: lift typed expr to fn sig
--  (ty, pExp) <- case (fnSig, rhsE) of
--    --(TyUnknown, P.Typed t e) -> (,e) <$> convTyM t
--      _ -> pure (fnSig, rhsE)
----let (ty , pExp) = (fnSig , rhsE)
--
--  iNames <- freshNames (length pats)
--  hNms <- zipWithM mkLArg iNames pats
--  case pExp of
--    P.PrimOp instr -> pure $ LInstr (CU.mkEntity fNm ty) instr
--    _ -> LBind (CU.mkEntity fNm ty) iNames <$> expr2Core pExp
--traverse (maybe (pure ()) rmHName) hNms

--mkSigMap :: V.Vector P.Decl -> ToCoreEnv (M.Map HName Type)
--mkSigMap sigs =
--    let f (P.TypeSigDecl nms ty) mp = convTyM ty >>= \t ->
--            pure $ foldr (\k m->M.insert (pName2Text k) t m) mp nms
--    in foldrM f M.empty sigs

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
  , isPolyFn       = const False
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
_parseTree2Core startConvState topImports (P.Module mName imports topBinds typeDecl parseDetails)
 = CoreModule
  { moduleName     = mName
  , algData        = dataTys
  , bindings       = binds
  , nTopBinds      = nTopBinds'
  , tyConInstances = V.empty
  , parseDetails   = ParseDetails {
      _classDecls     = classDecls'
--  , _defaults       = IM.empty
    , _fixities       = localFixities endState
    , _hNameBinds     = hNames   endState
    , _hNameTypes     = hTyNames endState
  }
  }
  where
  (binds, nTopBinds' , dataTys, classDecls') = val
  (val, endState) = runState toCoreM startConvState
  toCoreM = pure (V.empty, 0, V.empty , V.empty)

  toCoreM :: ToCoreEnv (BindMap, Int , TypeMap, V.Vector ClassDecl) = do
  -- Note. types and binds vectors must match iNames
  -- topBindings;typeDecls;localBindings;overloads;externs

    -- 1. register fixity declarations
--  modify (\x->x{localFixities=convFixities (P.fixities parseTree)})

    -- 2. data: get the constructors and dataEntities (name + dataty)
--  (cons, dataEntities) <- getTypesAndCons (P.tyAliases parseTree)
--  modify (\x->x{ _bindList = cons         : _bindList x
--               , _tyList   = dataEntities : _tyList x })

    -- 3. extern entities
--  let dataEntities = V.empty
--  externs <- mapM (doExtern dataEntities) (P.externs parseTree)
--  modify (\x->x{_bindList = (LExtern <$> externs) : _bindList x})

    -- 4. type functions:
--  tyFunINms<- V.fromList<$>freshTyNames (V.length (P.tyFuns parseTree))
--  (typeFuns, datas) <- V.unzip <$> V.zipWithM doTypeFun (P.tyFuns parseTree) tyFunINms
--  let datas' = V.foldl' (V.++) V.empty datas
--  modify (\x->x{ _tyList = datas' : typeFuns : _tyList x })

    -- 5. typeclasses
    -- note. classDecls includes local bindings (they must match iNames)
--  (classDecls, topClassFns)
--    <- doTypeClasses (P.classes parseTree) (P.classInsts parseTree)
    -- also take + clear locals from overloads + default functions
--  modify (\x->x{ _bindList  = localBinds x : topClassFns : _bindList x
--               , localBinds = V.empty
--               })

    -- 6. expression bindings
--    (hNSigMap :: M.Map HName Ty) <- mkSigMap (P.topSigs parseTree)
--    let findTopSig :: HName -> Maybe Ty = \hNm -> M.lookup hNm hNSigMap
    let findTopSig x = Nothing -- TODO
--  (fnBinds , nTopBinds)  <- getFns findTopSig (P.topBinds parseTree)
--  fnLocals <- gets localBinds
--  modify (\x->x{_bindList = fnLocals : fnBinds : _bindList x })

    -- 7. Collect results
    -- ! the resulting vectors must be consistent with all iNames !
--  binds      <- V.concat . reverse <$> gets _bindList
--  tyEntities <- V.concat . reverse <$> gets _tyList
    pure (V.empty, 0, V.empty, V.empty)

expr2Core :: P.TT -> ToCoreEnv Term =  \case
  P.VBind n -> pure $ Var n
  P.Lit l ->   pure $ case l of
    PolyInt{} ->  Instr MkNum  [Lit l]
    PolyFrac{} -> Instr MkReal [Lit l]
    _ -> Lit l -- do

  P.PrimOp primInstr ->
    let arity = 2
        ent = CU.lambdaBound
    in do
    i <- freshName
    addLocal i (LInstr ent primInstr)
    pure $ Var i

  P.App f args -> expr2Core f >>= \case
    Var fId -> App fId <$> mapM expr2Core args
    other   -> error $ "weird fn: " ++ show other

  P.InfixTrain leftExpr infixTrain -> 
    gets localFixities >>= \fixities ->
    let
    getFixity x = case Nothing of --case pQName2Text x `HM.lookup` fixities of
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
    handlePrec :: (P.TT, [(P.IName, P.TT)]) -> (P.IName, P.TT)
               -> (P.TT, [(P.IName, P.TT)])
    handlePrec (expr, []) (rOp, rExp) = (P.App (P.VLocal rOp) [expr, rExp] , [])
    handlePrec (expr, (lOp, lExp) : stack) next@(rOp, _) =
      if lOp `hasPrec` rOp -- getInfix rOp > getInfix lOp
      then (expr , next : (lOp, lExp) : stack)
      else handlePrec (P.App (P.VLocal lOp) [expr, lExp] , stack) next
    (expr', remOpStack) = foldl' handlePrec (leftExpr, []) infixTrain
    -- apply all ops remaining in opStack
    expr = let infix2App lExp (op, rExp) = P.App (P.VLocal op) [lExp, rExp]
           in foldl' infix2App expr' remOpStack
    in expr2Core $ expr

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
--  f :: ((PExp,PExp) -> Term.SwitchCase -> Term.SwitchCase)
    f (ifE, thenE) nextSwitch = mkSwitch ifE thenE (lFalse, nextSwitch)
    in mkSwitch lastIfE lastElseE (lFalse, Instr ExprHole []) >>= \lastSwitch ->
       foldrM f lastSwitch alts

  P.Case e alts  -> expr2Core e >>= getCaseAlts alts
  P.AsPat nm pat -> _
  P.WildCard     -> pure $ Instr ExprHole []
  P.TypeExp ty   -> _
  P.Typed t e    -> do -- we name it so we can type annotate it
    iNm <- freshName
    (ty , expr) <- -- CU.localState $
      (,) <$> convTyM t <*> expr2Core e
    addLocal iNm (LBind (CU.mkAnonEntity ty) [] expr)
    pure $ Var iNm
--P.SectionL
--P.SectionR

--P.Let pTree exp -> do
--  -- lets are modules, with the distinction that we still codegen them
--  -- , which is why they're assigned names immediately
--  tyCnt <- gets tyNameCount
--  nmCnt <- gets nameCount
--  let letConvState = emptyConvState {
--          tyNameCount = tyCnt
--        , nameCount = nmCnt }
--      pMod = P.Module (P.Ident T.empty) pTree
--      letMod = _parseTree2Core letConvState V.empty pMod
--  loc <- gets id
--  modify(\x->x{localModules=letMod : localModules x
--              , nameCount   = nameCount x + V.length (bindings letMod)
--              , tyNameCount = tyNameCount x + V.length (algData letMod)
--              , localBinds  = localBinds x V.++ bindings letMod
--              , _tyList     = algData  letMod : _tyList x
--              })
--  exp <- expr2Core exp
--  modify(\x->x{localModules = drop 1 (localModules x)})
--  pure exp

  other -> error ("unhandled expr: " ++ show other)

--incUse :: IName -> ToCoreEnv () = \n newBind ->
-- let doUpdate cm =
--      let binds = V.modify (\v->MV.write v n newBind) (bindings cm)
--      in  cm { bindings=binds }
-- in gets  modify (\x->x{ coreModule = doUpdate (coreModule x) })

-- getCaseAlts returns a partial constructor for a Term
-- biggest point is to accomodate both P.Case and P.LambdaCase cleanly
-- There are many patterns to handle here, and it is often necessary
-- to chain case expressions
--getCaseAlts :: [P.Alt] -> Term -> ToCoreEnv Term
-- = \alts e ->
--  -- dataCase: all alts have type (Name [Name] expr)
--  -- then it's a data decomposition
--  let 
--  -- Rearrange infixes into normal form
--  doInfixPats :: P.Pat -> P.Pat = \case
--    P.PInfixApp p1 n ps ->
--      let a = doInfixPats p1
--          b = doInfixPats ps
--      in doInfixPats $ P.PApp n (p1:[ps])
--    P.PApp qNm ps -> P.PApp qNm (doInfixPats <$> ps)
--    other -> other
--
--  doLitAlt = \case
--    P.PLit l -> _

--  convDecon :: P.Alt -> ToCoreEnv (Maybe (IName, [IName], Term))
--  convDecon (P.Alt pat pexp)
--   = case doInfixPats pat of
--    P.PVar nm -> _
--    P.PApp nm argPats -> _
----    lookupHNm (pQName2Text nm) >>= \case
----    Nothing -> error ("unknown Constructor:" ++ show nm)
----    Just n  -> let 
----        varOrNothing = \case { P.PVar n->Just (pName2Text n)
----                             ; _->Nothing }
----        args = case traverse varOrNothing argPats of
----              Just x -> x
----              Nothing -> error "failed to convert pattern"
----        registerLArg i hNm = addHName hNm i
----          *> addLocal i (LArg $ CU.mkLambdaBound hNm)
----      in do
----      iArgs <- freshNames (length args)
----      zipWithM registerLArg iArgs args
----      Just . (n, iArgs , ) <$> expr2Core pexp
--    P.PTuple args -> error "tuple in case" -- deconTuple
--    P.PLit l    -> pure Nothing
--    P.PList ps  -> _
--    P.PWildCard -> _
--  in do
--  dataCase <- sequence <$> mapM convDecon alts
--  pure $ case dataCase of
--    Just alts -> Case e (Decon alts)
--    Nothing   -> Case e $ Switch _ -- (doLitAlt <$> alts)

-- fixities
defaultPrec = 9
defaultFixity = Fixity defaultPrec LAssoc

convFixities = HM.empty
--convFixities :: V.Vector P.Decl -> HM.HashMap HName Fixity
--convFixities decls = 
--  let convAssoc = \case
--        P.AssocRight -> RAssoc
--        P.AssocNone  -> LAssoc
--        P.AssocLeft  -> LAssoc
--      convFixity = \case { Just i -> i ; Nothing -> defaultPrec }
--      infix2pair (P.InfixDecl a f [op])
--        = (pName2Text op , Fixity (convFixity f) (convAssoc a))
--  in HM.fromList $ V.toList $ infix2pair <$> decls
--

-}
