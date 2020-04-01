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
 BindType tyArgs set -> show tyArgs ++ " => " ++ show set

prettyVName = \case
    VArg i  -> "λ" ++ show i
    VBind i -> "π" ++ show i

prettyTerm = \case
    Var     v -> show v
    Lit     l -> show l
    App     f args -> "(" ++ show f ++ " " ++ intercalate " " (show <$> args) ++ ")"
    MultiIf ts -> "if " ++ show ts
    Instr   p -> "(" ++ show p ++ ")"

    Cons    ts -> "{" ++ show ts ++ "}"
    Proj    t f -> show t ++ " . " ++ show f
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
   in "[| " ++ s ++ " |]"

 THArray    t -> "@" ++ show t
 THArg      i -> "λ" ++ show i

 THIxType   t t2 -> "ixTy: " ++ show t ++ show t2
 THIxTerm   t termTyPairs -> "ixTerm: " ++ show t ++ show termTyPairs
 THEta      term ty -> "eta(" ++ show term ++ ":" ++ show ty ++")"

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
--ppType i = show
----ppType' = ppType (\x -> "$" ++ show x)
----ppType :: (IName -> String) -> Type -> String = \deref -> clCyan . \case
---- TyAlias nm      -> deref nm
---- TyRigid r       -> printf "rigid: %d(%v)" r (deref r)
---- TyMono m        -> case m of
----   MonoTyPrim lty  -> case lty of
----     other         -> show other
----   MonoSubTy r p i -> printf "subTy %d : %d <= %d" i r p
----
---- TyPoly p        -> show p
---- TyArrow tys     -> clNormal ++ "(" ++ (concat $ DL.intersperse " -> "
----                           (ppType deref <$> tys)) ++ ")"
------ TyPAp tys ty -> "PAp (" ++ ppType deref (TyArrow tys) ++ ") -> "
------                  ++ ppType deref (TyArrow tys)
---- t@TyFn{}   -> show t
---- TyUnknown       -> "TyUnknown"
---- TyBroken        -> "tyBroken"
---- other           -> show other
--
--ppCoreExpr :: (IName -> String) -> (IName -> String)
--           -> String -> Term -> String
-- = \deref derefTy indent ->
-- let ppCoreExpr' = ppCoreExpr deref derefTy indent
----     ppType'     = ppType derefTy
-- in \e -> case e of
--  Var n -> deref n
--  Lit l -> show l
--  App f args ->
--    let parenthesize x = "(" ++ ppCoreExpr' x ++ ")" 
--    in ppCoreExpr' f ++" "++ concat (DL.intersperse " " (parenthesize <$> args))
--  -- Let binds e -> error "let in coreexpr" --"let "++ppBinds (\x->Nothing) binds++"in "++ ppCoreExpr e
--  Case c a -> case a of
--    Switch alts -> "case "++ppCoreExpr' c++show alts
--  l -> show l
--
--ppDataAlt :: (IName -> String) -> String -> (IName, [IName], Term) -> String
--ppDataAlt deref indent (con, args, ret) = indent ++
-- deref con ++ (concatMap (\x -> " " ++ (deref x)) args) ++ " -> " ++ 
-- ppCoreExpr deref (\_->"fixpls") (indent++"  ") ret
--
--showMaybeName = \case { Just nm -> show nm ; Nothing -> "_" }
--
--ppBinds :: [Binding] -> (IName -> String) -> (IName -> String) -> String
-- = \l f derefTy -> concat $ zipWith (ppBind f derefTy "\n   ") [0..] l
--ppBind f derefTy indent lineNumber b =
--  let ppEntity' = ppEntity derefTy
--  in clGreen indent ++ show lineNumber ++ ": " ++ case b of
----  LTypeVar e -> "tyVar " ++ showMaybeName (named e) ++ ": " ++ show (typed e)
--  LBind entity args e -> showMaybeName (named entity)
--    ++ " " ++ show args 
--    ++ " : " ++ ppType derefTy (ty entity)
--    ++ {-indent ++-} " = " ++ ppCoreExpr f derefTy "" e
--  LArg a  -> "larg: "    ++ ppEntity' a
--  LCon a    -> "lcon: "    ++ ppEntity' a
--  LClass a b c-> "lclass: "  ++ ppEntity' a ++ " >= " ++ show b ++ show c
--  LExtern a -> "lextern: " ++ ppEntity' a
--  LInstr a instr -> "LInstr: " ++ ppEntity' a ++ " = " ++ show instr
--  Inline a e-> "inline: " ++ ppEntity' a ++ " = " ++ ppCoreExpr f derefTy "" e
--  LNoScope a -> "noscope: " ++ ppEntity' a
--
--ppCoreModule :: CoreModule -> String
-- = \(CoreModule hNm typeMap bindings n (ParseDetails classDecls {-defaults-} fixities _ _)) ->
--  let derefTy  i = bind2HName        (typeMap  V.! i) i
--      derefVar i = bind2HName (info (bindings V.! i)) i
--      ppEntity'  = ppEntity derefTy
--  in
--     clCyan "-- types --\n"
--  ++ concat (V.imap (\i x->show i ++ " " ++ ppEntity' x ++ "\n")typeMap)
--  ++ clGreen "\n-- Top bindings --"
--  ++ concat (V.imap (ppBind derefVar derefTy "\n") $ V.take n bindings)
--  ++ clGreen "\n-- externs --"
--  ++ concat (V.imap (\i->ppBind derefVar derefTy "\n" (n+i) ) $ V.drop n bindings)
----  ++ "\n\n" ++ clMagenta "-- defaults --\n" ++ show defaults
----  ++ "\n" ++ clRed "-- Class decls --\n"++ ppClassDecls classDecls
--
--ppClassDecls classDecls
-- = DL.intercalate "\n" $ show <$> V.toList classDecls
--
---- function to convert an entity to a stringname
--bind2HName entity i = case named entity  of
--       Just x -> T.unpack x
--       Nothing-> "%" ++ show i
--
----ppCoreBinds :: CoreModule -> String
---- = \cm
----   -> let binds = bindings cm
----          top = V.filter (\case { LBind{} -> True ; _ -> False }) binds
----      in concat ((ppBind (bind2HName binds) "\n") <$> top)
--
--ppEntity derefTy ent = --(Entity nm ty) = 
--  case named ent of
--    Just nm -> show nm
--    Nothing -> show ""
--  ++ " := " ++ ppType derefTy (ty ent)


