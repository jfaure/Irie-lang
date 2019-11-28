-- Type judgements: checking and inferring
-- http://pauillac.inria.fr/~remy/mlf/icfp.pdf
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/boxy-icfp.pdf

-- The goal is to check and/or infer the types of all top level bindings
-- (and the types (kinds) of the types.. etc)
--   * evaluate (static) dependent types
--   * type-check
--   * inference: reduce every type to an llvm.AST.Type

-- Inference can guess monotypes, but not polytypes

-- skolemization = remove existential quantifiers
--   boxy matching: fill boxes with monotypes
--   (no instantiation/skolemization)
--
-- Flexible Vs rigid
-- flexible = subsume a type (<=)
-- rigid    = all must be exactly the same type (=)


-- By design, boxy matching is not an equivalence relation:
-- it is not reflexive (that would require guessing polytypes)
-- neither is it transitive |s|~s and s~|s| but not |s|~|s|.
-- similarly, boxy subsumption is neither reflexive nor transitive


module TypeJudge where
import Prim
import CoreSyn as C
import PrettyCore
import qualified CoreUtils as CU

import qualified Data.Vector.Mutable as MV -- mutable vectors
import Control.Monad.ST
import qualified Data.Vector as V
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Data.Functor
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict
import Data.Char (ord)

--import qualified LLVM.AST.Constant as LC
--import qualified LLVM.AST as L
import Debug.Trace

dump :: TCEnv ()
dump = traceM =<< gets (ppCoreModule . coreModule)

data TCEnvState = TCEnvState -- type check environment
 { coreModule  :: CoreModule
 , errors      :: [TCError]
 }

type TCEnv a = State TCEnvState a

judgeModule :: CoreModule -> CoreModule
judgeModule cm =
  let startState = TCEnvState
        { coreModule = cm
        , errors     = []
        }
      handleErrors :: TCEnvState -> CoreModule
        = \st -> case errors st of
        [] -> coreModule st
        errs -> error $ show errs
      go = V.imapM (judgeBind cm) (bindings cm)
  in handleErrors $ execState go startState

-- functions used by judgeBind and judgeExpr
lookupBindM :: IName -> TCEnv Binding
 = \n -> CU.lookupBinding n <$> gets (bindings . coreModule)
typeOfM :: IName -> TCEnv Type
 = \n -> CU.typeOfBind n    <$> gets (bindings . coreModule)
lookupHNameM :: IName -> TCEnv (Maybe HName)
 = \n -> named . info . CU.lookupBinding n
          <$> gets (bindings . coreModule)
-- modify a binding's type annotation
updateBindTy :: IName -> Type -> TCEnv () = \n newTy ->
 let doUpdate cm =
      let binds = bindings cm
          b = CU.lookupBinding n binds
          newBind = b { info = (info b) { typed=newTy } }
          binds' = V.modify (\v->MV.write v n newBind) binds
      in cm { bindings=binds' }
 in modify (\x->x{ coreModule = doUpdate (coreModule x) })

updateBind :: IName -> Binding -> TCEnv () = \n newBind ->
 let doUpdate cm =
      let binds = V.modify (\v->MV.write v n newBind) (bindings cm)
      in  cm { bindings=binds }
 in modify (\x->x{ coreModule = doUpdate (coreModule x) })

-- Rule lambda: propagate (maybe partial) type annotations downwards
-- let-I, let-S, lambda ABS1, ABS2 (pure inference case)
judgeBind :: CoreModule -> IName -> Binding -> TCEnv ()
 = \cm bindINm ->
  let unVar = CU.unVar (algData cm)
  in \case
  LArg    i  -> pure () -- pure $ typed i
  LCon    i  -> pure () -- pure $ typed i
  LClass  i  -> pure () -- pure $ traceShowId $ typed i
  LExtern i  -> pure () -- pure $ typed i
  Inline i e -> pure ()
--LPAp  info args e -> trace "lpap" $ pure () -- only created from judged LBinds
  LBind inf args e -> 
    let judgeFnBind isPAp arrowTys = do
          zipWithM updateBindTy args arrowTys
          -- Careful with splitting off and rebuilding TyArrows
          -- to avoid nesting (TyArrow [TyArrow [..]])
          let retTy = case drop (length args) arrowTys of
                []  -> error "impossible"
                [t] -> t
                tys -> TyArrow tys
          judgedRetTy <- judgeExpr e retTy cm
          argTys      <- mapM typeOfM args
          let fnTy = case retTy of
                r@(TyArrow rTs) -> TyArrow (argTys ++ rTs)
                r -> TyArrow (argTys ++ [r])
        --if isPAp
        --then updateBind bindINm $ LPAp inf{typed=fnTy} args e
          updateBindTy bindINm fnTy
    in case unVar (typed inf) of
      TyArrow arrowTys -> judgeFnBind False arrowTys
--    TyPAp   arrowTys -> judgeFnBind True  arrowTys
      -- notFnTys can still be 'proxy' functions that pass on all args
      notFnTy -> judgeExpr e notFnTy cm >>= \ty -> case args of
        [] -> updateBindTy bindINm ty
        args -> do 
          -- 'proxy' functions eg. `f a = (+) 1 a` just pass on args.
          binds <- mapM lookupBindM args
          let argTys = typed . info <$> binds
              fnTy = TyArrow $ argTys ++ [ty]
          updateBindTy bindINm fnTy

-- type judgements
-- a UserType of TyUnknown needs to be inferred. otherwise check it.
judgeExpr :: CoreExpr -> UserType -> CoreModule -> TCEnv Type
 = \got expected cm ->
  let
      -- local shortcuts ommitting boilerplate arguments
      unVar :: Type -> Type = CU.unVar (algData cm)
      subsume' a b = subsume a b unVar
      judgeExpr' got expected = judgeExpr got expected cm

      -- case expressions have the type of their most general alt
      mostGeneralType :: [Type] -> Maybe Type =
       let mostGeneral :: Type -> Type -> Maybe Type = \t1 t2 ->
            if | subsume' t1 t2 -> Just t1
               | subsume' t2 t1 -> Just t2
               | True           -> Nothing
       in foldr (\t1 t2 -> mostGeneral t1 =<< t2) (Just TyUnknown)

      -- inference should never return TyUnknown
      -- ('got TyUnknown' fails to subsume)
      checkOrInfer :: Type -> Type
      checkOrInfer gotTy = case expected of
          TyUnknown -> case gotTy of
              TyUnknown -> error ("failed to infer a type for expression: " ++ show got)
              got' -> got'
          _ -> case subsume' gotTy expected of
              True -> gotTy
              False -> error ("subsumption failure:"
                              ++ "\nExpected: " ++ ppType' expected
                              ++ "\nGot:      " ++ ppType' gotTy)

  in checkOrInfer <$> case got of

  Lit l    -> pure $ expected
  WildCard -> pure expected
  -- prims must have an expected type, exception is made for ExtractVal
  -- since that is autogenerated by patternmatches before type is known.
  Instr p  -> case expected of
      TyUnknown -> error ("primitive has unknown type: " ++ show p)
      t         -> pure expected
  Var nm ->
    -- 1. lookup type of the var in the environment
    -- 2. in checking mode, update env by filling var's boxes
    let fillBoxes :: Type -> Type -> Type
        fillBoxes boxy TyUnknown = boxy -- pure inference case
        fillBoxes boxy known = case unVar boxy of
          TyUnknown -> known
          TyArrow tys -> known -- ok ?!
          t -> known
    in do
      bindTy <- typed . info <$> lookupBindM nm
      let newTy = fillBoxes bindTy expected
      updateBindTy nm newTy
      pure newTy

  -- APP expr: unify argTypes and remove left arrows from app expr
  -- TODO PAP, also check arities match
  -- Typeclass resolution
  App fn args ->
    let judgeApp arrowTys =
          let expArgTys = take (length args) arrowTys
              (consumedTys, remTys) = splitAt (length args) arrowTys
          in  zipWithM judgeExpr' args expArgTys
           >>= \judged -> if all id $ zipWith subsume' judged arrowTys
           then case remTys of
             -- fn takes more args than it's type (eg. printf)
             []  -> pure $ last arrowTys -- TODO ensure it's variadic
             [t] -> pure t
             tys -> pure $ TyPAp consumedTys remTys
           else error "cannot unify function arguments"
        judgeExtern eTys = judgeApp $ TyMono . MonoTyPrim <$> eTys

    in judgeExpr' fn TyUnknown <&> unVar >>= \case
      TyArrow arrowTys -> judgeApp arrowTys
      TyPAp    t1s t2s -> judgeApp $ t1s ++ t2s
      TyMono (MonoTyPrim (PrimExtern   eTys)) -> judgeExtern eTys
      TyMono (MonoTyPrim (PrimExternVA eTys)) -> judgeExtern eTys
      TyUnknown -> error ("failed to infer function type: "++show fn)
      t -> error ("not a function: "++show fn++" : "++show t)

----------------------
-- Case expressions --
----------------------
-- 1. all patterns must subsume the scrutinee
-- 2. all exprs    must subsume the return type
  Case ofExpr a -> case a of
   Switch alts ->
    let tys = mapM (\(pat, expr) -> judgeExpr' expr expected) alts
    in head <$> tys

-- dataCase: good news is we know the exact type of constructors
   Decon alts -> do
    exprTys <- mapM (\(_,_,expr) -> judgeExpr' expr expected) alts
    patTys  <- mapM (\(con,args,_) -> case args of
        [] -> judgeExpr' (Var con) expected
        _  -> judgeExpr' (App (Var con) (Var <$> args)) expected
      ) alts

    let expScrutTy = case mostGeneralType patTys of
            Just t -> t
            Nothing -> error "bad case pattern"
    scrutTy <- judgeExpr' ofExpr expScrutTy

    let patsOk = all (\got -> subsume' scrutTy got)  patTys
        altsOk = all (\got -> subsume' got expected) exprTys
    pure $ if patsOk && altsOk then expected
           else error (if patsOk then "bad Alts" else "bad pats")
    -- TODO what if we don't know the expected type (in altsOK) ?
    -- use mostGeneralType probably

  unexpected -> error ("panic: tyJudge: " ++ show unexpected)

-----------------
-- Subsumption --
-----------------
-- t1 <= t2 ? is a vanilla type acceptable in the context of a (boxy) type
-- 'expected' is a vanilla type, 'got' is boxy
-- note. boxy subsumption is not reflexive
-- This requires a lookup function to deref typeAliases
subsume :: Type -> Type -> (Type -> Type) -> Bool
subsume got exp unVar = subsume' got exp
  where
  -- local subsume with freeVar TyVarLookupFn
  subsume' gotV expV =
    let got = unVar gotV
        exp = unVar expV
    in case exp of
    TyMono exp' -> case got of
      TyMono got' -> subsumeMM got' exp'
      TyPoly got' -> subsumePM got' exp'
      a -> error ("subsume: unexpected type: " ++ show a ++ " : " ++ show exp)
    TyPoly exp' -> case got of
      TyMono got'  -> subsumeMP got' exp'
      TyPoly got'  -> subsumePP got' exp'
      a -> error ("subsume: unexpected type: " ++ show a)
    TyArrow tysExp -> case got of
      TyArrow tysGot -> subsumeArrow tysGot tysExp
      TyPoly PolyAny -> True
      _ -> False
    TyExpr _ -> _
    TyUnknown -> True -- 'got' was inferred, so assume it's ok
    other -> error ("panic: unexpected type: " ++ show other)

  subsumeArrow :: [Type] -> [Type] -> Bool
  subsumeArrow got exp = all id (zipWith subsume' got exp)

  subsumeMM :: MonoType -> MonoType -> Bool
  subsumeMM (MonoTyPrim t) (MonoTyPrim t2) = t == t2
  subsumeMM (MonoRigid r) (MonoRigid r2)   = r == r2

  subsumeMP :: MonoType -> PolyType -> Bool
   = \got exp            -> case exp of
    PolyAny              -> True
    PolyConstrain tys    -> all (`subsume'` (TyMono got)) tys
    PolyUnion  tys       -> any (`subsume'` (TyMono got)) tys
    PolyData p _         -> subsumeMP got p

  subsumePM :: PolyType  -> MonoType -> Bool
--subsumePM (PolyData p _) m@(MonoRigid r) = subsumeMP m p
  subsumePM _ _ = False -- Everything else is invalid

  subsumePP :: PolyType  -> PolyType -> Bool
   = \got exp            -> case got of
    PolyAny              -> True
    PolyConstrain gTys   -> _ -- all $ f <$> tys
    -- data: use the polytypes for subsumption
    PolyData p1 _        -> case exp of
      PolyData p2 _ -> subsumePP p1 p2
      _             -> False
    PolyUnion  gTys      -> case exp of
      PolyAny            -> False
      PolyConstrain eTys -> _
      PolyUnion  eTys    -> hasAnyBy subsume' eTys gTys -- TODO check order
    where

    hasAnyBy :: (a->a->Bool) -> [a] -> [a] -> Bool
    hasAnyBy _ [] _ = False
    hasAnyBy _ _ [] = False
    hasAnyBy f search (x:xs) = any (f x) search || hasAnyBy f search xs

    localState :: State s a -> State s a
    localState f = get >>= \s -> f <* put s
