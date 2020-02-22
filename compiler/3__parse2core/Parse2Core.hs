module Parse2Core where

import Prim
import CoreSyn
import qualified CoreUtils as CU
import qualified ParseSyntax as P
import qualified Data.Vector as V
import qualified Data.Vector.Generic.Mutable as MV
import qualified Data.Map as M
import Control.Monad.State
import Data.Foldable (foldl')
import Data.Functor
import Debug.Trace

parseTree2Core :: P.Module -> CoreModule
parseTree2Core (P.Module mNm imports rawBinds locals pds) = let
  importBinds = resolveImports (V.fromList imports)
  modBinds    = Left <$> V.fromList rawBinds
  nBinds      = V.length modBinds
  allBinds    = modBinds V.++ (Right <$> importBinds)
  binds = (\(Right x)->x) <$> execState (mapM (convBind nBinds) [0..nBinds]) allBinds
  in CoreModule {
      moduleName   = mNm
    , algData      = V.empty
    , bindings     = binds
    , nTopBinds    = V.length binds
    , parseDetails = ParseDetails V.empty M.empty M.empty M.empty
  }

resolveImports :: V.Vector P.ImportDecl -> V.Vector Binding
resolveImports imports = let
  externs = mkExtern <$> imports
  mkExtern x = case x of
    P.NoScope h -> LNoScope $ ent { named = Just h }
    _ -> LExtern $ ent {
      named = Just $ P.externName x ,
      ty    = TyJudged $ [THPrim $ P.externType x] }
  in externs

type ConvBind = Either P.TopBind Binding
type ConvState = State (V.Vector ConvBind)
updateBind :: IName -> ConvBind -> ConvState ()
updateBind i new = modify $ V.modify (\v->MV.write v i new)

convBind :: Int -> Int -> ConvState ()
convBind nBinds iName = gets (V.! iName) >>= \case
 Right _ -> pure () -- already done
 Left (P.FunBind hNm matches ty) -> let
  (args , tt) = matches2TT matches
  typeAnn = case ty of
    Nothing -> pure TyNone
    Just t -> convTT nBinds t <&> \case
      Left t     -> TyUser t
      Right term -> error $ "term given as type annotation: " ++ show term
  in do
    tyAnn <- typeAnn
    let inf = ent{named = Just hNm , ty=tyAnn}
        mkTyBind (Type uni t) = LetType uni inf args t
        bind = either mkTyBind (LBind inf args) <$> convTT nBinds tt
    updateBind iName =<< Right <$> bind

matches2TT :: [P.FnMatch] -> ([IName] , P.TT) = \case
  [P.FnMatch f e] -> ( , e) $ (\(P.PArg i) -> i) <$> f

convTT = _convTT (resolveInfixes _)
-- ambiguous cases (polymorphic abstractions) are returned as (types / terms ??)
_convTT :: _ -> _ -> P.TT -> ConvState (Either Type Term)
_convTT resolveInfixes nLocals =
  let convTT'   = _convTT resolveInfixes nLocals
      getUni  n = gets (uni . (V.! n))
  in \case
  P.Var v -> co
    (x , n) <- case v of
          P.VBind n   -> (Var n , n)
          P.VExtern n -> let n' = n + nLocals in (Var n' , n')
          P.VLocal n  -> (Arg n , n)
    in x

  P.Lit l   -> pure . Right $ case l of
    PolyInt{}  -> Instr MkNum  [Lit l]
    PolyFrac{} -> Instr MkReal [Lit l]

  P.InfixTrain leftExpr infixApps -> convTT' $ resolveInfixes leftExpr infixApps
  P.App f args -> let
    term  = \case { Left x -> error "type in app" ; Right term -> term }
    fn    = \case { Var i -> i } . term <$> convTT' f
    in case fn of 
      Right (Var i) -> let
        args' = mapM (fmap term . convTT') args
        in Right <$> (App <$> fn <*> args')
      Left  (THArg i) -> let
        mkTyFn (THArg i) \case
          Right -> THIndexed (THArg i) . head <$> args'
          Left  -> THLam (THArg i) . head <$> args'

        in foldlM mkTyFn args'

  x -> error $ "not yet: " ++ show x

resolveInfixes :: _ -> P.TT -> [(P.TT,P.TT)] -> P.TT
resolveInfixes hasPrec leftExpr infixTrain = let
  -- 1. if rOp has lower prec then lOp then add it to the opStack
  -- 2. else apply infix from the opStack
  -- 3. when no more rOp's, Apply remaining infixes from the opStack
  _ `hasPrec` _ = True -- TODO
  handlePrec :: (P.TT, [(P.TT, P.TT)]) -> (P.TT, P.TT)
             -> (P.TT, [(P.TT, P.TT)])
  handlePrec (expr, []) (rOp, rExp) =
    (P.App rOp [expr, rExp] , [])
  handlePrec (expr, (lOp, lExp) : stack) next@(rOp, _) =
    if lOp `hasPrec` rOp
    then (expr , next : (lOp, lExp) : stack)
    else handlePrec (P.App lOp [expr, lExp] , stack) next
  (expr, remOpStack) = foldl' handlePrec (leftExpr, []) infixTrain

  -- apply remaining opStack
  infix2App lExp (op, rExp) = P.App op [lExp, rExp]
  in foldl' infix2App expr remOpStack
