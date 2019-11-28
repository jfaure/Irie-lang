module LlvmHsExts (constZero, charPtrType, unknownPtrType,
                   sizeof, globalStringPtr)
where 

import LLVM.AST hiding (function)
import LLVM.AST.Type as AST
--import qualified LLVM.AST.Float as F
--import qualified LLVM.AST.Typed as T
import qualified LLVM.AST.Constant as C
--import qualified LLVM.AST.IntegerPredicate as P
--import qualified LLVM.AST.FloatingPointPredicate as Pf
import LLVM.AST.Global
import LLVM.AST.Typed
import LLVM.AST.Linkage
--import LLVM.AST.Typed
import LLVM.AST.AddrSpace
import LLVM.IRBuilder.Module
import Data.Char (ord)

-- Some constants
constZero :: Operand
constZero = ConstantOperand $ C.Int 32 0
charPtrType :: LLVM.AST.Type
charPtrType = PointerType (IntegerType 8) (AddrSpace 0)
unknownPtrType = charPtrType -- The conventional bitcastable void* pointer in llvm

-- platform independant sizeof: a gep to the end of a nullptr and some bitcasting.
sizeof :: LLVM.AST.Type -> C.Constant
sizeof t = C.PtrToInt szPtr (IntegerType 32)
  where
     ptrType = PointerType t (AddrSpace 0)
     nullPtr = C.IntToPtr (C.Int 32 0) ptrType
     szPtr   = C.GetElementPtr True nullPtr [C.Int 32 1]

-- while i wait for my PR to llvm-hs to be accepted
globalStringPtr
  :: (MonadModuleBuilder m)
  => String       -- ^ The string to generate
  -> Name         -- ^ Variable name of the pointer
  -> m C.Constant
globalStringPtr str nm = do
  let asciiVals = map (fromIntegral . ord) str
      llvmVals  = map (C.Int 8) (asciiVals ++ [0]) -- append null terminator
      char      = IntegerType 8
      charStar  = ptr char
      charArray = C.Array char llvmVals
      ty        = LLVM.AST.Typed.typeOf charArray
  emitDefn $ GlobalDefinition globalVariableDefaults
    { name                  = nm
    , LLVM.AST.Global.type' = ty
    , linkage               = Private
    , isConstant            = True
    , initializer           = Just charArray
    , unnamedAddr           = Just GlobalAddr
    }
  return $ C.GetElementPtr True (C.GlobalReference (ptr ty) nm) [(C.Int 32 0), (C.Int 32 0)]
