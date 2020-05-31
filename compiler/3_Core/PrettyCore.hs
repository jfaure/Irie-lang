{-# LANGUAGE OverloadedStrings #-}
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

------------
-- Pretty --
------------

prettyBind = \case
 WIP -> "WIP"
 BindTerm args term ty -> show args ++ " => " ++ show term ++ clGreen (" : " ++ show ty)
 BindType tyArgs set -> show tyArgs ++ " =: " ++ show set

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
    Match   ts d -> "\\case" ++ "| "
      ++ intercalate " | " (show <$> M.toList ts) ++ " |_ " ++ show d
    List    ts -> "[" ++ (concatMap show ts) ++ "]"

prettyTyHead = \case
 THPrim     p -> show p
 THVar      i -> "Λ" ++ show i
 THImplicit i -> "∀" ++ show i
 THAlias    i -> "π" ++ show i
 THExt      i -> "E" ++ show i

 THArrow    args ret -> intercalate " → " $ show <$> (args ++ [ret])
 THRec      t-> "μ" ++ show t
 THProd     prodTy -> let
   showField (f , t) = show f ++ ":" ++ show t
   p = intercalate " ; " $ showField <$> M.toList prodTy
   in "{" ++ p ++ "}"
 THSum      sumTy ->  let
   showLabel (l , t) = show l ++ "#" ++ show t
   s  = intercalate " | " $ showLabel <$> M.toList sumTy
   in " | " ++ s ++ " | "

 THArray    t -> "@" ++ show t
 THArg      i -> "λ" ++ show i

-- THIxType   t t2 -> "ixTy: " ++ show t ++ show t2
-- THIxTerm   t (t2,ty) -> "ixTerm: " ++ show t ++ " $ (" ++ show t2 ++ " : " ++ show ty ++ ")"
-- THEta      term ty -> "eta(" ++ show term ++ ":" ++ show ty ++")"
 THIx t deps -> show t ++ " $$ " ++ (intercalate " $$ " $ show <$> deps)

 THSet   uni -> "Set" ++ show uni

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
