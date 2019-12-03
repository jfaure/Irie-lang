{-# LANGUAGE StrictData #-}
-- StgSyn: Most of the haskell data types used in lfvm
-- See StgToLLVM for a detailed description of how this maps to llvm
module StgSyn where

import qualified LLVM.AST -- (Operand, Instruction, Type, Name)
import qualified LLVM.AST.Constant -- (Constant)
import qualified Data.Vector as V

data StgModule = StgModule
 { stgData  :: V.Vector StgData          -- alg data
 , typeDefs :: V.Vector (StgId, StgType) -- type aliases
 , binds    :: V.Vector StgBinding       -- constants|functions|extern
 }
--note. aliases: if we emit the definition, then the simple
-- alias name will be a valid llvm type

-- let bindings: data def | function def | extern decl
-- Data definitions: These require 2 functions:
--   1. llvm constructor function
--   2. a codeGen decon function that resolves sumType tags and
--      unpacks (LLVM gep + letBind) struct members
-- **************
-- * Leaf types *
-- **************
-- [StgOps]: some llvm Instructions have flags, but stg only cares about operands.
type StgConst = LLVM.AST.Constant.Constant
type StgSsa   = LLVM.AST.Operand
type StgId    = LLVM.AST.Name
type StgUnOp  = LLVM.AST.Operand -> LLVM.AST.Instruction
type StgBinOp = LLVM.AST.Operand -> LLVM.AST.Operand -> LLVM.AST.Instruction
type StgFn    = LLVM.AST.Operand

data StgType  -- All these must eventually become llvm equivalents
 = StgLlvmType  LLVM.AST.Type -- Vanilla type (could still be a struct)
 | StgTypeAlias StgId         -- resolved using typeMap during codegen
-- StgTypeRef: Internally we store alias+type for StgAlgTypes
-- aliases: we save the initial type to tell later (if its a fn/struct)
 | StgTyperef   LLVM.AST.Type LLVM.AST.Type
 | StgFnType    [StgType]     -- stg function type (not extern)
 | StgAlgType   StgData       -- Algdata - by far the most complex
 | StgTuple     [LLVM.AST.Type]
 | StgPApTy     [StgType] [StgType]
 -- polytypes
 | StgPolyType  StgId   -- just a name, valid types must be bitcasted
-- | StgSubType   StgType -- ty is ok here, but must be bitcasted

-- StgArg = resolves (stgToIR) to an ssa passable to an llvm function
-- Note. this includes function pointers!
data StgArg
  = StgConstArg  StgConst -- constant value
  | StgSsaArg    StgSsa   -- used only by union tags in case atm.
  | StgVarArg    StgId    -- ref to an SSA (or 0 arity function)
  | StgExprArg   StgExpr  -- full expr

-- Alg data is modeled as a sum type: it may have 0 alts or 0 fields.
-- the sumType tag corresponds to the alts, in the order defined
type StgData        = StgSumType -- Alg data
data StgProductType = StgProductType StgId [StgType]
data StgSumType     = StgSumType     StgId [StgProductType]

data StgBinding = StgBinding StgId StgRhs
data StgRhs
 -- function expr
 = StgTopRhs   [StgArg]  -- Arg Names
               [StgType] -- Arg Types
               StgType   -- return Type
               StgExpr   -- Function body
 -- closure: function uses free vars, to be passed as extra arguments
 -- | StgClosure  FreeVars [StgArg] [StgType] StgType StgExpr
 | StgExt      LLVM.AST.Type -- extern function
 | StgRhsConst StgConst -- become global constants
 | StgRhsSsa   StgSsa   -- used internally for locals (esp.function arguments)
 | StgPrim StgPrimitive [StgType] StgType

data FreeVars = FreeVars [(StgArg, StgType)]

data StgPrimitive
 = StgPrim1   StgUnOp
 | StgPrim2   StgBinOp
 | StgMkTuple
 | StgGep

 | StgExtractVal Int -- like llvm, except will also deref pointers
 | StgPAp
 | StgPApApp Int

data StgExpr
  = StgLit  StgArg

 -- StgInstr: inline form for internal use. prefer StgApp (via StgRhs)
 -- coresyn lifts/names primitives so they can be given a type
 -- Used only for ExtractVal on patterns and StgPap
  | StgInstr StgPrimitive [StgArg]

  | StgApp  StgId     -- rhs name (incl. primitives)
            [StgArg]  -- args (maybe empty)

  | StgLet  [StgBinding]
            StgExpr

  | StgCase StgExpr         -- scrutinee
            (Maybe StgExpr) -- default. (eg. error *> exit)
            StgCaseAlts     -- Switch or Data deconstruction

data StgCaseAlts
 = StgSwitch    [(LLVM.AST.Constant.Constant, StgExpr)] -- values -> alt
 | StgDeconAlts [(StgId, [StgId], StgExpr)] -- decon [args] -> alt

-- Cheap show instances
instance Show StgModule
  where
  show (StgModule stgData aliases binds) =
    "-- Data --\n"
    ++ (concatMap (\x-> show x ++ "\n\n") stgData)
    ++ "\n-- Aliases --\n"
    ++ (concatMap (\x-> show x ++ "\n") aliases)
    ++ "\n-- Bindings --\n"
    ++ (concatMap (\x-> show x ++ "\n") binds)

instance Show StgPrimitive where
 show =
  let z = LLVM.AST.ConstantOperand LLVM.AST.Constant.TokenNone
  in \case
  StgPrim2 f  -> "primBinOp: " ++ show (f z z)
  StgPrim1 f -> "primUnOp: " ++ show (f z)
  StgGep -> "#!gep"
  StgMkTuple  -> "#!MkTuple"
  StgExtractVal i -> "internal ExtractVal " ++ show i
  StgPApApp arity -> "#! papApp " ++ show arity
  StgPAp    -> "#! pap"
deriving instance Show StgExpr
deriving instance Show StgCaseAlts
deriving instance Show StgSumType
deriving instance Show StgProductType
deriving instance Show StgType
instance Show StgRhs where
 show = \case
  StgTopRhs args tys retty e -> "top: " ++ show args ++ show e
    ++ "\n : " ++ show tys ++ show retty
  StgRhsSsa s                    -> "closure: " ++ show s
  StgExt t                       -> "extern " ++ show t
  StgRhsConst l                  -> "const: " ++ show l
  StgPrim p t r                  -> "prim: " ++ show p ++ " : " ++ show t ++ " -> " ++ show r
instance Show StgBinding
  where show (StgBinding id rhs) = show id ++ " = " ++ show rhs ++ "\n"
deriving instance Show StgArg
