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
--
-- despite dependent types, core seperates terms and types
-- source/origin annotations (for error msgs)

module CoreSyn where

import Prim

import qualified Data.Vector        as V
import qualified Data.Text          as T
import qualified Data.List          as DL -- intersperse
import qualified Data.IntMap.Strict as IM

type IName   = Int
type NameMap = V.Vector
type HName   = T.Text -- human readable name

type TypeMap      = NameMap Entity
type BindMap      = NameMap Binding
type DefaultDecls = IM.IntMap MonoType

-- note. algData is dataTypes     ++ aliases
--       bindings is constructors ++ binds
type ClassFns = IM.IntMap Binding  -- indexed by polymorphic classFn's Iname
type ClassInsts = IM.IntMap ClassFns
type ClassOverloads = IM.IntMap ClassInsts
data CoreModule = CoreModule {
   algData  :: TypeMap -- data and aliases

 -- binds incl. constructors, locals, and class Fns (not overloads!)
 , bindings :: BindMap
 , externs  :: TypeMap -- extern declarations

 -- typeclass resolution, indexed by the class polytype's iName
 , overloads :: ClassOverloads
 -- typeclass resolution when multiple Monotypes are possible
 , defaults  :: IM.IntMap MonoType -- eg. default Num Int

-- , tyFuns :: V.Vector TypeFunction
-- , copied :: Map IName Int -- track potentially copied data

 -- lookup table (for the interpreter)
 --, hNameBinds :: Data.Map HName IName
 --, hNameTypes :: Data.Map HName IName
 }

-- Binding: save argNames brought into scope
-- since all vars get a unique name, we need this for locals,
-- note. top binds/data are always in scope, so no need.
data Binding
-- let bindings assigned to a coreExpr
 = LBind {
   args  :: [IName] -- the unique arg Names used by 'expr'
 , expr  :: CoreExpr
 , info  :: Entity  -- hname, type, source
 }
-- vars coming into scope (via lambda, case expr, and expr+typesig)
 | LArg { info :: Entity }
-- Term level GADT constructor (Type is known)
 | LCon { info :: Entity }
 | LClass { info :: Entity } -- classFn declaration

-- an entity = info about | coreExpr | fn arg | decon arg
data Entity = Entity { -- entity info
   named    :: Maybe HName
 , typed    :: Type -- also terms (in a type context)
-- , source :: Maybe SourceEntity
 }

-- source info
--data SourceEntity = SourceEntity 
-- { src :: Maybe srcLoc
-- }

data CoreExpr
 = Var IName
 | Lit Literal
 | Instr PrimInstr
 | App CoreExpr [CoreExpr]
 | SwitchCase CoreExpr [(Literal, CoreExpr)]
 | DataCase CoreExpr
            [(IName, [IName], CoreExpr)] -- Con [args] -> expr
 | TypeExpr Type -- as return of `TypeFunction`
 | WildCard      -- TODO move to Literal

----------- Types -- ---------
type UserType = Type -- user supplied type annotation
data Type
 = TyAlias IName   -- aliases (esp. to MonoTyData)

 | TyMono  MonoType -- monotypes 't'
 | TyPoly  PolyType -- constrained polytypes 'p', 's'
 | TyArrow [Type]  -- Kind 'function' incl. Sum/Product cons

 | TyExpr  TypeFunction -- incl. dependent types

 | TyUnknown -- needs to be inferred - the so-called box type.
 | TyBroken -- typecheck couldn't infer a coherent type

-- Note. data is up to stg, Core only handles GADT-style sigs
-- TODO subtypes, (.) accessor
-- ! These types cannot be instantiated with Polytypes
-- they are polymorphic only as return types of TypeFunctions
-- Note. coresyn datas save their own name,
--       it's easier to convert to stg that way
data MonoType
 = MonoTyPrim   PrimType
 | MonoTyData   HName [(HName, [Type])] --TODO Type as tyArrow ?
 -- TODO rm this and simply gen getters in tocore (and record updates ?)
 | MonoTyRecord HName [(HName, [(HName, Type)])]
 | MonoTyTuple  [Type]
 | MonoTyClass -- ?!

type PolyType = Forall
data Forall -- typeclass & and | operations
 = ForallAnd [Type] -- (&) multiple typeclass constraints
 | ForallOr  [Type] -- (|) union types (esp. type of typeclass)
 | ForallAny        -- Existential type (since typevars are flexible)

-- type functions: from trivial `data a = ..` to dependent types
-- TODO kind functions, type matching, type classes, subtypes
-- If a TyDependent returns a new data,
--   we must emit it as a TyFn during ToCore (to access constructors etc..)
data TypeFunction
 = TyDependent {
   tyArgs :: [IName]
 , tyExpr :: CoreExpr -- : CoreExpr.TypeExpr
 }
 | TyTrivialFn { -- trivial case: App (Con n) (TypeExp e)
   tyArgs :: [IName]
 , tyVal  :: Type
 }

----------- Types -- --------- 
-- type vars are flexible = arbitrary types rather than variables.
-- boxy matching: fill boxes with monotypes
--   (no instantiation/skolemization)
--
-- By design, boxy matching is not an equivalence relation:
-- it is not reflexive (that would require guessing polytypes)
-- neither is it transitive |s|~s and s~|s| but not |s|~|s|.
-- similarly, boxy subsumption is neither reflexive nor transitive

deriving instance Show Forall
deriving instance Show Binding
deriving instance Show MonoType
deriving instance Show Type
deriving instance Show TypeFunction
deriving instance Show CoreExpr
deriving instance Show Entity
deriving instance Show CoreModule

typeOfLiteral :: Literal -> Type
typeOfLiteral l = TyUnknown

data TCError
 = UnifyFail { expected :: Entity, got :: Entity}
 deriving (Show)

ppType :: Type -> String = \case
 TyAlias nm -> "$" ++ show nm
 TyMono m -> case m of
   MonoTyPrim lty -> case lty of
     other -> show other
   MonoTyData nm cons -> "data.$" ++ show nm

 TyPoly p -> show p
 TyArrow tys -> "(" ++ (concat $ DL.intersperse " -> " 
                                (ppType <$> tys)) ++ ")"
 TyExpr coreExpr -> error "tyexpr"
 TyUnknown -> "TyUnknown"
 TyBroken  -> "tyBroken"

ppCoreExpr :: (IName -> String) -> String -> CoreExpr -> String
 = \deref indent ->
 let ppCoreExpr' = ppCoreExpr deref indent
 in \e -> case e of
  Var n -> {- show n ++-} deref n
  Lit l -> show l
  App f args -> ppCoreExpr' f ++" "++ concat (DL.intersperse " " ((\x -> "(" ++ ppCoreExpr' x ++ ")" ) <$> args))
  -- Let binds e -> error "let in coreexpr" --"let "++ppBinds (\x->Nothing) binds++"in "++ ppCoreExpr e
  SwitchCase c alts -> "case " ++ ppCoreExpr' c ++ show alts
  DataCase c alts -> "case " ++ ppCoreExpr' c ++ " of" ++ "\n" ++ (concat $ DL.intersperse "\n" $ (ppDataAlt deref (indent++"  "))<$> alts)
  TypeExpr ty -> show ty
  l -> show l

ppDataAlt :: (IName -> String) -> String -> (IName, [IName], CoreExpr) -> String
ppDataAlt deref indent (con, args, ret) = indent ++
 deref con ++ (concatMap (\x -> " " ++ (deref x)) args) ++ " -> " ++ 
 ppCoreExpr deref (indent++"  ") ret

ppBinds :: [Binding] -> (IName -> String) -> String
 = \l f -> concatMap (ppBind f "\n   ") l
ppBind f indent b = indent ++ case b of
  LBind args e entity -> case named entity of
     { Just nm -> show nm ; Nothing -> "_" }
    ++ " " ++ show args 
    ++ " : " ++ ppType (typed entity)
    ++ {-indent ++-} " = " ++ ppCoreExpr f "" e
  LArg a -> "larg: " ++ ppEntity a
  LCon a -> "lcon: " ++ ppEntity a
  LClass a -> "lclass: " ++ ppEntity a

ppCoreModule :: CoreModule -> String
 = \(CoreModule typeMap bindings externs overloads defaults)
  ->  "-- types --\n" ++ (concatMap (\x->ppEntity x ++ "\n") typeMap)
      ++ "\n" ++ "-- defaults --\n" ++ show defaults

      ++ "\n\n" ++ "-- bindings --"
      ++ concat ((ppBind (bind2HName bindings) "\n") <$> bindings)
      ++ "\n\n" ++ "-- overloads --"
      ++ "\n" ++ DL.intercalate "\n" (ppClassOverloads <$> IM.elems overloads)
      ++ "\n\n" ++ "-- externs --"
      ++ "\n" ++ (concatMap (\x->ppEntity x ++ "\n") externs)

ppClassOverloads overloads = DL.intercalate "\n" (show <$> IM.elems overloads)

-- function to convert a  binding to a stringname
bind2HName bindings i = case named $ info $ (bindings V.! i) of
       Just x -> T.unpack x
       Nothing-> "%" ++ show i

ppCoreBinds :: CoreModule -> String
 = \cm
   -> let binds = bindings cm
          top = V.filter (\case { LBind{} -> True ; _ -> False }) binds
      in concat ((ppBind (bind2HName binds) "\n") <$> top)

ppEntity (Entity nm ty) = 
  case nm of
    Just nm -> show nm
    Nothing -> "_"
  ++ " : " ++ ppType ty -- ++ " (" ++ show uni ++ ")"
