module PrettyCore where

import Prim
import CoreSyn

import qualified Data.Vector        as V
import qualified Data.Text          as T
import qualified Data.List          as DL
import qualified Data.IntMap.Strict as IM
import qualified Data.Map as M
import Data.List (intercalate)
import Text.Printf
import Debug.Trace

instance Show VName where show = prettyVName
instance Show Term where show = prettyTerm
instance Show TyHead where show = prettyTyHead
instance Show Bind where show = prettyBind

deriving instance Show Expr
deriving instance Show BiSub
deriving instance Show Kind
deriving instance Show Pi

instance Show LC where
 show lc = go False lc where
  go depth = let parens x = if depth then "(" ++ x ++ ")" else x
   in \case
    LCArg i -> "ωλ" ++ show i 
    LCApp f a -> parens (go True f ++ " " ++ go True a)
    LCTerm t y -> parens ("ωTerm " ++ show t ++ " : " ++ show y)
    LCRec i  -> parens $ "ωμ" ++ show i -- ++ " : " ++ show ty

tyExpr = \case
  Ty t -> t
  expr -> error $ "expected type, got: " ++ show expr

------------
-- Pretty --
------------

prettyBind = \case
 WIP -> "WIP"
 BindOK args (Core term ty) -> show args ++ " => " ++ show term ++ clGreen (" : " ++ prettyTy ty)
 BindOK tyArgs (Ty set) -> show tyArgs ++ " =: " ++ show set
 BindOK args (ULC lc)  -> show args ++ " =  " ++ show lc

prettyVName = \case
    VArg i  -> "λ" ++ show i
    VBind i -> "π" ++ show i

prettyTerm = \case
    Var     v -> show v
    Lit     l -> show l
    App     f args -> "(" ++ show f ++ " $ " ++ intercalate " " (show <$> args) ++ ")"
    MultiIf ts t -> "if " ++ show ts ++ " else " ++ show t
    Instr   p -> "(" ++ show p ++ ")"

    Cons    ts -> let
      sr (label , val) = show label ++ "@" ++ prettyTerm val
      in "{ "
        ++ (intercalate " ; " (sr <$> M.toList ts))
        ++ " }"
    Proj    t f -> show t ++ "." ++ show f
    Label   l t -> show l ++ "@" ++ show t
    Match   ts d -> let
      showLabel (l , t) = show l ++ " => " ++ show t
      in "\\case" ++ "| "
        ++ intercalate " | " (showLabel <$> M.toList ts) ++ " |_ " ++ show d
    List    ts -> "[" ++ (concatMap show ts) ++ "]"

prettyTy = \case
  [x] -> show x
  x ->   show x
prettyTyHead = \case
 THPrim     p -> show p
 THVar      i -> "τ" ++ show i
-- THImplicit i -> "∀" ++ show i
 THAlias    i -> "π" ++ show i
 THExt      i -> "E" ++ show i

 THArrow    [] ret -> error $ "panic: fntype with no args: [] → (" ++ prettyTy ret ++ ")"
 THArrow    args ret -> "(" ++ intercalate " → " (prettyTy <$> (args ++ [ret])) ++ ")"
 THRec      t-> "μ" ++ show t
 THRecApp   t a-> "μ$" ++ show t ++ " " ++ (intercalate " $ " $ show <$> a)
 THProd     prodTy -> let
   showField (f , t) = show f ++ ":" ++ show t
   p = intercalate " ; " $ showField <$> M.toList prodTy
   in "{" ++ p ++ "}"
 THSum      sumTy ->  let
   showLabel (l , t) = show l ++ "#" ++ show t
   s  = intercalate "\n  | " $ showLabel <$> M.toList sumTy
   in " 〈" ++ s ++ " 〉"

 THArray    t -> "@" ++ show t
 THArg      i -> "λ" ++ show i
 THLamBound i -> "Λ" ++ show i

-- THIxType   t t2 -> "ixTy: " ++ show t ++ show t2
-- THIxTerm   t (t2,ty) -> "ixTerm: " ++ show t ++ " $ (" ++ show t2 ++ " : " ++ show ty ++ ")"
-- THEta      term ty -> "eta(" ++ show term ++ ":" ++ show ty ++")"
-- THIx t deps -> show t ++ " $$ " ++ (intercalate " $$ " $ show <$> deps)
 THPi ars t arsMap -> "∏" ++ show ars ++ " (" ++ prettyTy t ++ " where " ++ show arsMap ++ ")"
 THSi ars t arsMap -> "Σ" ++ show ars ++ " (" ++ prettyTy t ++ " where " ++ show arsMap ++ ")"
-- THCore t ty -> "↑(" ++ show t ++ " : " ++ show ty ++ ")" -- term in type context

 THSet   uni -> "Set" ++ show uni
 THInstr i ars -> show i ++ show ars
 THULC l -> show l

clBlack   x = "\x1b[30m" ++ x ++ "\x1b[0m"
clRed     x = "\x1b[31m" ++ x ++ "\x1b[0m" 
clGreen   x = "\x1b[32m" ++ x ++ "\x1b[0m"
clYellow  x = "\x1b[33m" ++ x ++ "\x1b[0m"
clBlue    x = "\x1b[34m" ++ x ++ "\x1b[0m"
clMagenta x = "\x1b[35m" ++ x ++ "\x1b[0m"
clCyan    x = "\x1b[36m" ++ x ++ "\x1b[0m"
clWhite   x = "\x1b[37m" ++ x ++ "\x1b[0m"
clNormal = "\x1b[0m"

-- Notes --
{-   The lambda-bound types here are flexible ie. subsumption can occur before beta-reduction.
  This can be weakened by instantiation to a (monomorphically abstracted) typing scheme
  We unconditionally trust annotations so far as the rank of polymorphism, since that cannot be inferred (we cannot insert type abstractions)
-}
