module MixfixSyn where
data Assoc = Assoc | AssocLeft | AssocRight | AssocNone deriving Eq
data Prec = Prec { assoc :: Assoc , prec :: Int }
defaultPrec = Prec AssocLeft 10
type MFIName = IName -- index into mixfixwords vector
type MFWords = [Maybe IName]
type QMFWords = [Maybe (IName , IName)]
type ModIName = IName
data MixfixDef = MixfixDef {
 -- the actual binding is on the holey name: "_+_" , "if_then_else_"
   mixfixBind :: IName
 , mfWords    :: MFWords
 , fixity     :: Prec
}

data MFWord -- points to it's binding
  = StartPrefix  MixfixDef IName
  | StartPostfix MixfixDef IName
  | MFPart       IName

-- module context needs to be recoverable during mixfix parsing
data QMFWord -- qualified
  = QStartPrefix  MixfixDef (ModIName , IName)
  | QStartPostfix MixfixDef (ModIName , IName)
  | QMFPart       (ModIName , IName)

mfw2qmfw modNm = \case
  StartPrefix  m i -> QStartPrefix  m (modNm , i)
  StartPostfix m i -> QStartPostfix m (modNm , i)
  MFPart         i -> QMFPart         (modNm , i)

deriving instance Show Assoc
deriving instance Show Prec
deriving instance Show MixfixDef
deriving instance Show MFWord
deriving instance Show QMFWord
