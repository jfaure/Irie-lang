module TTCalculus (ttApp) where
import Prim
import CoreSyn
--import Errors
import Externs
import CoreUtils
import TCState
import Data.List(span)
import Control.Lens

-- Application of TTs: TTs can be promoted to higher universes, but not demoted
-- Types can be indexed by Terms, but can never again be terms themselves
-- Lambda calculus TTs are ambiguous, eg. 'f x = x' could be a type or a term
-- This has to be done in TCState because forward refs may trigger inference mid ttApp
ttApp :: (Int -> TCEnv s Expr) -> (ExternVar -> TCEnv s Expr) -> Expr -> [Expr] -> TCEnv s Expr
ttApp readBind handleExtern fn args = let --trace (clYellow (show fn <> " $ " <> show args :: Text)) $ let
 getQBind q = use thisMod >>= \modIName -> use externs >>= \e ->
   handleExtern (readQParseExtern modIName e (modName q) (unQName q))
 ttApp' = ttApp readBind handleExtern
 doApp coreFn args = let
   (termArgs , otherArgs) = span (\case {Core{}->True ; _->False}) args
   app = App coreFn $ (\(Core t _ty)->t) <$> termArgs -- forget the argument types
   in pure $ case otherArgs of
     [] -> Core app _ -- don't forget to set retTy
     tys -> if any isPoisonExpr tys then PoisonExpr else error $ "ttApp cannot resolve application: " <> show app <> show tys

--   x    -> error $ "ttApp cannot resolve application: " <> show app <> show x

 in case fn of
   PoisonExpr -> pure PoisonExpr
   ExprApp f2 args2 -> (ttApp' f2 args2) >>= \f' -> ttApp' f' args
   Core cf ty -> case cf of
     Var (VBind i) -> readBind i >>= \e -> case did_ e of
       Core (Var (VBind j)) ty | j == i -> doApp cf args
       f -> ttApp' f args
     Var (VQBind q) -> getQBind q >>= \case
       Core (Var (VQBind j)) ty | j == q -> doApp cf args
       e -> ttApp' e args

--   Special instructions (esp type constructors)
     Instr (TyInstr Arrow)  -> expr2Ty readBind `mapM` args <&> \case
       { [a , b] -> Ty (TyGround (mkTyArrow [a] b)) }
     Instr (TyInstr MkIntN) | [Core (Lit (Int i)) ty] <- args -> pure $ Ty (TyGround [THPrim (PrimInt $ fromIntegral i)])
     Instr (MkPAp n) | f : args' <- args -> ttApp' f args'
     coreFn -> doApp coreFn args
   Ty f -> case f of -- (dependent pair) / Sigma / Existential type
     x -> error $ "ttapp panic: " <> show x <> " $ " <> show args
   _ -> error $ "ttapp: not a function: " <> show fn <> " $ " <> show args
