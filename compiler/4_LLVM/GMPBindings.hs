module GMPBindings where

import Prim
import Prim2LLVM
import qualified Data.Map as M
import qualified LLVM.AST as L
import qualified LLVM.AST.Type as LT
import qualified LLVM.AST.Constant as C
import LLVM.AST.Global
import LLVM.AST.Linkage as L

data GMPDefs = GMPDefs {
  initGMP_MPZ :: L.Operand
 ,ops     :: M.Map IntInstrs (Maybe L.Operand)
}

intInstr2GMP :: IntInstrs -> L.Name = \case
  Add -> "__gmpz_mul"
  Sub -> "__gmpz_sub"
  Mul -> "__gmpz_mul"
  SDiv -> "__gmpz_div"

-- gmp
--(typeDefmpz , tympz' , tympz) = structTypeDef "mpz_t" [intType , intType , voidPtrType]

initMPZ maybeInit = _ -- do
--mpz <- alloca' tympz'
--f   <- gets (initGMP_MPZ)
--f `call'` [mpz]

genGMPInstr instr a b = do
  fn <- declareGMPBinOp (intInstr2GMP instr)
  r  <- initMPZ Nothing
  r <$ fn `call'` [r , a , b]

declareGMPBinOp nm = let
  defn = L.GlobalDefinition $ functionDefaults {
    name = nm
  , linkage = L.External
  , parameters = ([] , True)
  , returnType = LT.VoidType
  }
  funty = LT.ptr $ LT.FunctionType LT.VoidType [] True
  fnOp  = L.ConstantOperand $ C.GlobalReference funty nm
  in fnOp <$ emitDef defn
