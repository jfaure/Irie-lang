{-# Language TemplateHaskell #-}
module FusionEnv where
import CoreSyn
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import qualified Data.Map as M
import Control.Lens

data RecFn
 = Cata    Term -- term successfully rewritten as a (higher-order) Cata
 | Stream  Term -- ie. unstream < f < stream
 | Unboxed Term -- no data
 | Weird   Term -- mixes second-order cata and stream

-- The big question: How much arg structure is needed for a specialisation to fuse something
data FuseArg -- Which args are case-split and how
 = NoBranch  -- Not case-split in this function (Presumably its built into the result and may be case-split later)
 | CaseArg   -- arg is case-split
 | CaseFnArg FuseArg -- arg is a fn whose result is case-split (upto given structure)

 | LensedArg {- Lens -} -- What structure of the arg must be known to fuse with a case

-- Re-use specialisations if the structure is identical
data ArgShape
 = ShapeNone
 | ShapeLabel ILabel [ArgShape]
 | ShapeQBind QName
 deriving (Eq , Ord , Show)

getArgShape = \case
  Label l params -> ShapeLabel l (getArgShape <$> params)
  Var (VQBind q) -> ShapeQBind q
  _ -> ShapeNone

type SimplifierEnv s = StateT (Simplifier s) (ST s)
data Simplifier s = Simplifier {
   _thisMod     :: IName
 , _extBinds    :: V.Vector (V.Vector Expr)
 , _cBinds      :: MV.MVector s Bind
 , _nApps       :: Int -- approximate complexity rating of a function
 , _argTable    :: MV.MVector s Term -- used for β reduction
 , _useArgTable :: Bool -- toggle for bypassing argTable (ie. if not simplifying the body of an App)
 , _bruijnArgs  :: V.Vector Term
 , _self        :: Int    -- the bind we're simplifying

 , _nSpecs      :: Int -- cursor for allocating new specialisations
 , _prevSpecs   :: Int -- specialisations already computed; new requests are: [prevSpecs .. nSpecs-1]
 , _tmpSpecs    :: MV.MVector s (Either QName IName , Int , [Term]) -- requested specialisations of q (bind) or i (spec)
 , _letSpecs    :: MV.MVector s (Maybe Term)  -- specialisations
 , _bindSpecs   :: MV.MVector s BitSet -- specialisation INames for each bind (to avoid respecialising things)
 , _cachedSpecs :: MV.MVector s (M.Map [ArgShape] IName) -- recover specialisations for same arg shapes
 -- recursive specialisations
 , _thisSpec    :: IName  -- wip spec
 , _recSpecs    :: BitSet -- specialisations that contain themselves (don't inline these)

  -- collect fns using specialisations not yet generated; will have to resimplify later
 , _hasSpecs    :: BitSet
 , _reSpecs     :: [IName] -- Bindings containing un-inlined specialisations

 , _specStack   :: BitSet -- Avoid recursive inline
 , _inlineStack :: BitSet -- Avoid recursive inline

 , _caseArgs    :: BitSet
 , _caseFnArgs  :: BitSet
}; makeLenses ''Simplifier

--data ArgKind
--  = APrim PrimType
--  | AFunction [ArgKind] ArgKind
--  | ARecord   (IntMap ArgKind)
--  | ASum      (IntMap SumRep)
--  | APoly
--  | ARec -- only in Array or Tree (also fn return | any covariant position?)
--data SumRep = Enum | Peano | Wrap | Array [ArgKind] | Tree [ArgKind]
