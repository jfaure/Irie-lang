{-# LANGUAGE TemplateHaskell #-}
module TCState where
import CoreSyn
import CoreUtils
import Prim
import qualified Scope (Params)
import Externs
import Errors
import Control.Lens(makeLenses , use , (%=) , (.=))
import qualified Data.Vector.Mutable as MV ( MVector, grow, length, write, read )
import qualified ParseSyntax as P ( FnDef )
import qualified Data.Vector as V ( Vector )
import qualified BiUnify (biSubType , BisubEnvState(..))
import Generalise (generalise)

-- inference uses a cataM (biunification vector and new tvar assignments)
type TCEnv s a = StateT (TCEnvState s) (ST s) a
data TCEnvState s = TCEnvState {
 -- in
   _externs  :: Externs     -- vector ExternVars
 , _loadedMs :: V.Vector LoadedMod
 , _thisMod  :: ModuleIName -- used to make the QName for local bindings
 , _topBindsCount :: Int    -- offset in modBinds where module binds end and their lifted let-bindings begin

 -- out
 , _modBinds :: MV.MVector s (LetMeta , Bind) -- all lets lifted, the P.FnDef is saved in letBinds
 , _errors   :: Errors

 -- Inference state
 , _scopeParams   :: Scope.Params
 , _letBinds      :: MV.MVector s (MV.MVector s P.FnDef)-- (Either P.FnDef Bind))
 , _letNest       :: Int
 , _bindsBitSet   :: BitSet -- mark inferred binds
 , _inferStack    :: BitSet -- To detect infer cycles: recursion / mutuals
 , _cyclicDeps    :: BitSet
 , _bruijnArgVars :: V.Vector Int       -- bruijn arg -> TVar map

 -- Biunification state
 , _tmpFails      :: [TmpBiSubError]    -- bisub failures are dealt with at an enclosing App
 , _blen          :: Int                -- cursor for bis which may have spare space
 , _bis           :: MV.MVector s BiSub -- typeVars

 -- Free vars => any VBruijns from outside the let-binding must be explicitly passed as new VBruijns
 , _freeLimit   :: Int
 , _letCaptures :: BitSet
 , _captureRenames :: MV.MVector s Int -- undef unless letCaptures bit set!
}; makeLenses ''TCEnvState

-- Simply copy over the relevant parts of tcstate
-- TODO make a struct for these
bisub :: Type -> Type -> TCState.TCEnv s BiCast
bisub got exp = use blen >>= \bl -> use bis >>= \bvec -> let
  runBiSub = runStateT (BiUnify.biSubType got exp) BiUnify.BisubEnvState
    { BiUnify._blen = bl , BiUnify._bis = bvec , BiUnify._tmpFails = [] }
  in lift runBiSub >>= \(val , BiUnify.BisubEnvState{BiUnify._blen=bl , BiUnify._bis=bvec , BiUnify._tmpFails=tf})
    -> val <$ do
    TCState.tmpFails %= (tf ++)
    TCState.bis .= bvec
    TCState.blen .= bl

generaliseType :: Type -> TCEnv s Type
generaliseType ty = use blen >>= \bl -> use bis >>= \bis' -> lift (generalise bl bis' ty)

clearBiSubs :: Int -> TCEnv s ()
clearBiSubs n = blen .= n

-- spawn new tvar slots in the bisubs vector
-- ! duplicated in biunify
freshBiSubs :: Int -> TCEnv s [Int]
freshBiSubs n = do
  bisubs <- use bis
  biLen  <- use blen
  let tyVars  = [biLen .. biLen+n-1]
  blen .= biLen + n
  bisubs <- if MV.length bisubs < biLen + n then MV.grow bisubs n else pure bisubs
  bis .= bisubs
  tyVars `forM_` \i -> MV.write bisubs i (BiSub tyBot tyTop)
  pure tyVars

expectedType :: Expr -> TCEnv s ()
expectedType notTy = (errors . checkFails %= (ExpectedType notTy :))

resolveTypeQName = exprToTy <=< resolveQIndex

-- All forward/mutuals must be solved already! ie. don't use on TT QNames
resolveQIndex :: forall s. QName -> TCEnv s Expr
resolveQIndex q = use thisMod >>= \mI -> if modName q == mI
  then use modBinds >>= \mBinds -> MV.read mBinds (unQName q) <&> \(_lm , BindOK _ e) -> e
  else use loadedMs <&> \lBinds -> fromMaybe (error "invalid QName?!")
    (readQName lBinds (modName q) (unQName q))

termToTy :: Term -> TCEnv s Type
termToTy = let
  reduceInstr t args = case t of
    TyInstr MkIntN | [Lit (Fin _ i)] <- args -> pure $ tHeadToTy (THPrim (PrimInt $ fromIntegral i))
    TyInstr Arrow  | [arg , ret] <- args ->
      (\a b -> tHeadToTy $ THTyCon (THArrow [a] b)) <$> termToTy arg <*> termToTy ret
    x -> error $ "bad ty instr: " <> show x <> "<\n" <> show args
  in \case
  Ty t -> pure t
  Prod xs -> traverse termToTy xs <&> \ts -> TyGround [THTyCon (THProduct ts)]
  Var (VQBindIndex q) -> pure (tHeadToTy (THAlias q))
  VBruijn i -> pure (tHeadToTy (THBound i))
  App (Var (VQBindIndex q)) args -> resolveQIndex q >>= \case
    Core (Instr t) _ -> reduceInstr t args
    Core (Var (VQBindIndex q2)) _ | q2 == q -> error $ "qname resolves to itself: " <> show q
    x -> exprToTy x
  App (Instr t) args -> reduceInstr t args
  t -> tyBot <$ expectedType (Core t tyBot)

exprToTy :: Expr -> TCEnv s Type
exprToTy (Core term _tyty) = termToTy term
