module Eval where
import Prim
import CoreSyn
import CoreUtils
import Data.Align
import Data.These
import ShowCore()
import qualified Data.IntMap as IM
import qualified Data.Vector.Mutable as MV

simplifyBinds e jbs = (\(BindOK c) -> BindOK (simplifyExpr e jbs c)) <$> jbs
simplifyExpr exts jbs = \case
  Core e t -> Core (simplifyTT exts jbs e) t
  x -> x

-- Always inline simple functions
-- Constant fold casts and up to scrutinees as much as possible (can have huge impact)
-- Const args valuable for function
-- eta reduction on lambdas

-- Case merge
-- exitification (float exit paths out of recursive functions)
-- liberate-case (unroll recursive fns once to avoid repeated case on free vars)
-- Pow app
simplifyTT externs jbs = \case
  App (Var (VBind i)) args -> _
  x -> x

etaReduce :: [IName] -> [Term] -> Term -> Term
etaReduce argNms args body = let
  argList = alignWith (\case { These a b -> (a,b) ; x -> error $ "unaligned args: " <> show (argNms , args) }) argNms args
  argMap  = IM.fromList argList
  etaReduce' argMap tt = let etaReduce'' = etaReduce' argMap
    in case tt of
    Var (VArg i) | Just sub <- argMap IM.!? i -> sub
    Var{}      -> tt
    Instr{}    -> tt
    Cast BiEQ t-> etaReduce'' t
    Cast c    t-> Cast c (etaReduce'' t)
    Lit{}      -> tt
    App f1 args1 -> case (etaReduce'' f1) of
      App (Instr (MkPAp n)) (f2 : args2) -> let diff = n - length args in case compare 0 diff of
        LT -> let (ok , rest) = splitAt diff (etaReduce'' <$> args2)
              in App (App (Instr (MkPAp diff)) ok) rest
        _  -> App f2 (etaReduce'' <$> (args1 ++ args2))
--      EQ -> App f2 (args1 ++ args2)
--      GT -> _ -- return function
      f -> App f (etaReduce'' <$> args1)
    TTLens term fields lensOp -> TTLens (etaReduce'' term) fields lensOp
    Abs{}      -> error $ "eta reduce: " <> show tt
    Cons c     -> Cons (etaReduce'' <$> c)
    Label{}    -> error $ "eta reduce: " <> show tt
    Match{}    -> error $ "eta reduce: " <> show tt
    _          -> error $ "eta reduce: " <> show tt
  in etaReduce' argMap body

type SimplifierEnv s = StateT (Simplifier s) (ST s)
data Simplifier s = Simplifier {
   cBinds   :: MV.MVector s Bind
 , nApps    :: Int
 , argTable :: MV.MVector s [Term] -- used for eta reduction
}

setNApps :: Int -> SimplifierEnv s ()
setNApps n = (modify $ \x->x{nApps = n})
zeroNApps :: SimplifierEnv s Int
zeroNApps= gets nApps <* (modify $ \x->x{nApps = 0})
incNApps :: SimplifierEnv s ()
incNApps = modify $ \x->x{nApps = 1 + nApps x}

simplifyBindings :: Int -> Int -> MV.MVector s Bind -> ST s (Simplifier s)
simplifyBindings nArgs nBinds bindsV = do
  argEtas <- MV.replicate nArgs []
  execStateT (simpleBind `mapM` [0 .. nBinds-1]) Simplifier {
    cBinds   = bindsV
  , nApps    = 0 -- measure the size of the callgraph
  , argTable = argEtas
  }

simpleBind :: Int -> SimplifierEnv s Bind
simpleBind n = gets cBinds >>= \cb -> MV.read cb n >>= \b -> do
--traceM "\n"
  svN <- zeroNApps
  MV.write cb n (BindOpt (0xFFFFFF) (Core (Var (VBind n)) [])) -- recursion guard
  new <- case b of
    BindOpt nApps body -> setNApps nApps *> pure body
    BindOK (Core t ty) -> simpleTerm t <&> \case
      -- catch top level partial application (ie. extra implicit args)
      App (Instr (MkPAp n)) (f2 : args2) -> let
        (arTs , retT) = getArrowArgs ty
        diff = n - length args2
        in Core (PartialApp arTs f2 args2) retT
      newT -> Core newT ty
    x -> pure $ PoisonExpr
  napps <- gets nApps <* setNApps svN
  let b = BindOpt napps new
  MV.write cb n (BindOpt napps new)
  pure b

simpleTerm :: Term -> SimplifierEnv s Term
simpleTerm t = let
  foldAbs argDefs' free body ty args = let
    (argDefs , trailingArgs , etaReducable) = partitionThese (align argDefs' args)
    in gets argTable >>= \aT -> do
      etaReducable `forM` \((i,ty) , arg) -> MV.modify aT (arg:) i
      tRaw <- simpleTerm body
      let t = case trailingArgs of { [] -> body ; ars -> App body ars }
      etaReducable `forM` \((i,ty) , arg) -> MV.modify aT (drop 1) i -- TODO what if stacking insertions ?
      pure $ case argDefs of
        []      -> t
  in case t of
  Var v -> case v of
    VBind i -> simpleBind i <&> \case
      BindOpt napps (Core new t) -> if False && napps < 1 then new else Var (VBind i) -- directly inline small callgraphs
    VArg  i -> gets argTable >>= \at -> MV.read at i <&> fromMaybe t . head
    x -> pure (Var x)

  Cast c a -> pure t

  Abs argDefs' free body ty -> simpleTerm body <&> \b -> Abs argDefs' free b ty

  App f args -> incNApps *> case f of
    Abs argDefs' free body ty -> foldAbs argDefs' free body ty args
    Instr i -> (simpleTerm `mapM` args) <&> \args -> case i of
      GMPInstr j -> simpleGMPInstr j args
      Zext | [Lit (Int i)]   <- args -> Lit (Fin 64 i)
           | [Lit (Fin n i)] <- args -> Lit (Fin 64 i)
      i -> App f args
    fn -> simpleTerm fn >>= \case
      Abs argDefs' free body ty -> foldAbs argDefs' free body ty args
      fn -> App fn <$> (simpleTerm `mapM` args)
  _ -> pure t

simpleGMPInstr :: NumInstrs -> [Term] -> Term
simpleGMPInstr i args = let
  mkCmpInstr pred args = App (Instr (NumInstr (PredInstr pred))) args
  in case i of
  IntInstr Add
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args -> App (Instr (GMPOther AddUI)) [Lit (Fin 64 i) , larg]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Sub
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args -> App (Instr (GMPOther UISub)) [Lit (Fin 64 i) , rarg]
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args -> App (Instr (GMPOther SubUI)) [larg , Lit (Fin 64 i)]
    | _ <- args -> App (Instr (GMPInstr i)) args
  IntInstr Mul
    -- ? MulUI
    | [Lit (Fin 64 i) , rarg] <- args -> App (Instr (GMPOther MulSI)) args
    | [larg , Lit (Fin 64 i)] <- args -> App (Instr (GMPOther MulSI)) [Lit (Fin 64 i) , larg]
  PredInstr LECmp -- TODO other cmp types
    -- CMPAbsD CMPAbsUI
    -- TODO spawn the icmp instruction here
    | [Cast (CastInstr (GMPZext n)) (Lit (Int i)) , rarg] <- args ->
        mkCmpInstr GECmp [App (Instr (GMPOther CMPUI)) [rarg , Lit (Fin 64 i)] , Lit (Fin 32 0)] -- flip the icmp
    | [larg , Cast (CastInstr (GMPZext n)) (Lit (Int i))] <- args ->
        mkCmpInstr LECmp [App (Instr (GMPOther CMPUI)) [larg , Lit (Fin 64 i)] , Lit (Fin 32 0)]
  IntInstr IPow
    -- powmui ?
    | [Lit (Fin 64 _) , Lit (Fin 64 _)] <- args -> App (Instr (GMPOther UIPowUI)) args
    | [larg , Lit (Fin 64 _)]           <- args -> App (Instr (GMPOther PowUI)) args
  -- nothing to fold
  i -> App (Instr (GMPInstr i)) args
