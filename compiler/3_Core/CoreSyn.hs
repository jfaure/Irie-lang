-- Core Language
-- recall: ParseSyn >> CoreExpr >> STG codegen
-- The language for type judgements: checking and inferring
--
-- ParseSyn vs Core
-- > no local variables
-- > all vars have a unique name
-- > no free variables (explicit function arguments)
-- > all entities are annotated with a type (can be TyUnknown)
-- - ultimately stg must have only monotypes

{-# LANGUAGE TemplateHaskell #-}
module CoreSyn
where

import Prim

import qualified Data.Vector         as V
import qualified Data.Text           as T
import qualified Data.IntMap.Strict  as IM
import qualified Data.Map.Strict as M
import qualified Data.IntSet as IS
import Data.List
import Control.Lens hiding (List)
import Data.STRef
import Control.Monad.ST
import Control.Monad.Primitive

type HName     = T.Text -- human readable name
type IName     = Int    -- Int name: index into bind|type vectors
type BiSubName = Int    -- index into bisubs
type IField    = Int  -- product-type fields index
type ILabel    = Int  -- sum-type labels     index

data VName
 = VBind IName -- bind   map
 | VArg  IName -- bisub  map
 | VExt  IName -- extern map (and prim instrs)

data Term
 = Var     VName
 | Lit     Literal
-- | Abs     [IName] 
 | App     Term    [Term] -- IName [Term]
 | MultiIf [(Term , Term)]
 | Instr   PrimInstr

 -- data constructions
 | Cons    (M.Map IField Term)
 | Proj    Term IField
 | Label   ILabel [Term] -- labels are heterogeneous lists
 | Match   (M.Map ILabel Term) (Maybe Term)
 | List    [Term]

-- Types are sampled from a
-- coproduct of profinite distributive lattices
-- typing schemes contain the monotypes of lambda-bound terms
-- a 'monotype' can be a typevar pointing to a polytype
-- type polarity corresponds to input(-) vs output(+)
type Type     = TyPlus
type Uni      = Int
type Set      = Type -- Set Uni Type
type TyCo     = [TyHead] -- same    polarity
type TyContra = [TyHead] -- reverse polarity
type TyMinus  = [TyHead] -- input  types (lattice meet) eg. args
type TyPlus   = [TyHead] -- output types (lattice join)

-- bisubs always reference themselves, so the mu. is implicit
data BiSub = BiSub { _pSub :: [TyHead] , _mSub :: [TyHead] }
newBiSub = BiSub [] []
type BiSubs = V.Vector BiSub -- indexed by TVars

-- components of the profinite distributive lattice of types
data TyHead -- head constructors for types.
 = THVar         BiSubName  -- index into bisubs
 | THAlias       IName      -- index into bindings
 | THArg         IName      -- lambda bound
 | THImplicit    IName      -- implicit lambda bound
 | THExt         IName      -- index into externs

 | THPrim     PrimType
 | THArrow    [TyContra] TyCo
 | THRec      IName TyCo  -- guarded and covariant in a 
   -- (ie. `Ma. (a->bool)->a` ok, but not `Ma. a->Bool`)
 | THProd     ProdTy
 | THSum      SumTy --incl tuples (~= var arity sum alt)
 | THArray    TyCo

 | THIxType   Type Type
 | THIxTerm   Type (Term , Type)

 | THIx       Expr
 | THEta      Term Type -- term is universe polymorphic (?!)

 | THHigher   Uni -- eg Set1
 -- Dynamic residue of types after erasure ?
type ProdTy = M.Map IField TyCo
type SumTy  = M.Map ILabel [TyCo]

-- non-regular recursion ?
-- isorecursive non-regular: add opaque roll/unroll primitives

-- label for the different head constructors
data Kind = KPrim | KArrow | KVar | KSum | KProd | KAny

-----------------------------
-- BiUnification datatypes --
-----------------------------
-- tagged tt
data Expr
 = Core Term Type
 | Ty   Type  -- Set0
 | Set  Uni Type

data Bind -- indexes in the bindmap
 = WIP
 | BindTerm [IName] Term Type
 | BindType [Expr] Set

-- | BindType [Expr] [Expr] Set -- implicit args first

makeLenses ''BiSub

expr2Ty = \case
  Core t ty -> ty
  Ty   t    -> _
  Set  i t  -> _
tyExpr = \case
  Ty t -> t
  _ -> _

instance Show VName where show = prettyVName
instance Show Term where show = prettyTerm
instance Show TyHead where show = prettyTyHead
instance Show Bind where show = prettyBind

deriving instance Show Expr
deriving instance Show BiSub
deriving instance Show Kind

deriving instance Eq Kind

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
 THRec      i ty  -> _
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
 THEta      term ty -> error "eta"

 THHigher   uni -> "Set" ++ show uni

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
