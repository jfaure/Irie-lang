module LlvmHsExts (constZero, charPtrType, unknownPtrType,
                   sizeof, globalStringPtr, externStringPtr, privateFunction)
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

import LLVM.IRBuilder.Monad
import Control.Monad

-- Some constants
constZero :: Operand
constZero = ConstantOperand $ C.Int 32 0

charTy = IntegerType 8

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
      llvmVals  = map (C.Int 8) (asciiVals ++ [0]) -- null terminator
      charStar  = ptr charTy
      charArray = C.Array charTy llvmVals
      ty        = LLVM.AST.Typed.typeOf charArray
  emitDefn $ GlobalDefinition globalVariableDefaults
    { name                  = nm
    , LLVM.AST.Global.type' = ty
    , linkage               = Private
    , isConstant            = True
    , initializer           = Just charArray
    , unnamedAddr           = Just GlobalAddr
    }
  pure $ C.GetElementPtr True (C.GlobalReference (ptr ty) nm) [(C.Int 32 0), (C.Int 32 0)]

externStringPtr :: (MonadModuleBuilder m)
 => String -> Name -> m C.Constant
externStringPtr strVal iden =
  let charArray = C.Array charTy llvmVals
      ty        = LLVM.AST.Typed.typeOf charArray
      llvmVals = (C.Int 8) <$> ((fromIntegral . ord) <$> strVal) ++ [0]
  in do
  failStrDecl <- emitDefn $ GlobalDefinition globalVariableDefaults
   { name    = iden
   , LLVM.AST.Global.type'= ty
   , linkage = Private
   , isConstant = True
   , initializer = Just charArray
--   , unnamedAddr = Just GlobalAddr
   }
  pure $ C.GetElementPtr True (C.GlobalReference (ptr ty) iden)
                              [(C.Int 32 0) , (C.Int 32 0)]


privateFunction
  :: MonadModuleBuilder m
  => Name  -- ^ Function name
  -> [(Type, ParameterName)]  -- ^ Parameter types and name suggestions
  -> Type  -- ^ Return type
  -> ([Operand] -> IRBuilderT m ())  -- ^ Function body builder
  -> m Operand
privateFunction label argtys retty body = do
  let tys = fst <$> argtys
  (paramNames, blocks) <- runIRBuilderT emptyIRBuilder $ do
    paramNames <- forM argtys $ \(_, paramName) -> case paramName of
      NoParameterName -> fresh
      ParameterName p -> fresh `named` p
    body $ zipWith LocalReference tys paramNames
    return paramNames
  let
    def = GlobalDefinition functionDefaults
      { name        = label
      , parameters  = (zipWith (\ty nm -> Parameter ty nm []) tys paramNames, False)
      , returnType  = retty
      , basicBlocks = blocks
      , linkage     = LinkOnce
      }
    funty = ptr $ FunctionType retty (fst <$> argtys) False
  emitDefn def
  pure $ ConstantOperand $ C.GlobalReference funty label
