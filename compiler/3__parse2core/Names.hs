-- Names become complex when imported core modules are in play
-- imports consist mostly of
--  * type and data declarations
--  * extern declarations
--  * class decls + instances
-- to import something, all it's local refs must be imported

module Names where
import CoreSyn
import qualified ParseSyntax as P

import qualified Data.Vector         as V
import qualified Data.Text           as T
import qualified Data.Map.Strict     as M
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict  as IM
import Control.Monad.Trans.State.Strict
import Data.Functor
import Control.Applicative
import Data.Foldable
import Debug.Trace

type ToCoreEnv a = State ConvState a

data ConvState = ConvState {
   imports       :: V.Vector CoreModule --Imports -- imports in scope
 , localFixities :: HM.HashMap HName Fixity
 , nameCount     :: IName
 , tyNameCount   :: IName
 , isPolyFn      :: (IName -> Bool) -- classFn's are contained within here

 , hNames        :: HM.HashMap HName IName
 , hTyNames      :: HM.HashMap HName IName

 , _tyList       :: [V.Vector Entity]
 , _bindList     :: [V.Vector Binding]
-- , _defaults     :: IM.IntMap MonoType

 , localBinds    :: V.Vector Binding
-- , localTys      :: V.Vector Entity

 , localModules  :: [CoreModule] -- letStack
 , toCoreErrors  :: ToCoreErrors
}

data Imports = Imports {
-- letImports  :: [CoreModule]
   openImports :: [CoreModule]
 , qualImports :: HM.HashMap HName CoreModule -- incl importas
-- , customImport :: ImportCustom -- hiding / renaming imports
}
--data ImportCustom = ImportCustom {
--   customMod :: Name
-- , hiding  :: Name
-- , renaming :: [(Name , Name)]
--}

data ToCoreErrors = ToCoreErrors {
   notInScope :: [P.IName]
}
noErrors = ToCoreErrors []

pName2Text = id

--insertLookup kx x t = HM.insertLookupWithKey (\_ a _ -> a) kx x t

addLocalTy  :: IName -> Entity -> ToCoreEnv IName =
 \iNm ty -> do
--  modify (\x->x{localTys=(localTys x `V.snoc` ty)})
  tys <- gets _tyList
  let h : end = tys
      h' = h `V.snoc` ty
      tys' = h' : end
  modify (\x->x{_tyList = tys'})
  pure iNm
addLocal    :: IName -> Binding -> ToCoreEnv IName =
  \iNm bind -> do
--  modify (\x->x{localBinds=V.snoc (localBinds x) bind })
  modify (\x->x{localBinds= localBinds x `V.snoc` bind })
  pure iNm

------------------------
-- Functions on Names -- 
------------------------
-- Fresh
freshNames :: Int -> ToCoreEnv [IName] = \count ->
  gets nameCount >>= \n ->
  modify (\x -> x{nameCount = n+count})   *> pure [n..n+count-1]
freshTyNames :: Int -> ToCoreEnv [IName] = \count ->
  gets tyNameCount >>= \n ->
  modify (\x -> x{tyNameCount = n+count}) *> pure [n..n+count-1]
freshName :: ToCoreEnv IName = gets nameCount >>= \n ->
  modify (\x->x{nameCount = n+1}) *> pure n
freshTyName :: ToCoreEnv IName = gets tyNameCount >>= \n ->
  modify (\x->x{tyNameCount = n+1}) *> pure n

-- AddNames
addHName , addTyHName :: T.Text -> IName -> ToCoreEnv ()
addHName hNm nm = modify (\x->x{hNames = HM.insert hNm nm (hNames x)})
addTyHName hNm nm=modify (\x->x{hTyNames= HM.insert hNm nm (hTyNames x)})

rmHName , rmTyHName :: T.Text -> ToCoreEnv ()
rmHName hNm   = modify (\x->x{hNames = HM.delete hNm (hNames x)})
rmTyHName hNm = modify (\x->x{hTyNames = HM.delete hNm (hTyNames x)})

-- mkFindHName, mkFindTyHName :: ToCoreEnv (HName -> Maybe IName)
-- mkFindHName   = gets hNames   <&> flip HM.lookup
mkFindTyHName :: ToCoreEnv (HName -> Maybe IName)
mkFindTyHName = gets hTyNames <&> flip HM.lookup

-- !!! lookups have an important additional function of bringing in
-- relevant bindings from imported modules to current modules
lookupHNm, lookupTyHNm :: HName -> ToCoreEnv (Maybe IName)
lookupName   n = lookupHNm   (pName2Text n)
lookupTyName n = lookupTyHNm (pName2Text n)

lookupHNm hNm = gets hNames >>= \hs -> case (hs `localLookup` hNm) of
  Nothing-> gets (asum . (letLookup hNm <$>) . localModules) {- >>= \case
    Nothing -> gets imports >>= (`moduleLookup` hNm)
    x -> pure x
    -}
  x->pure x

letLookup hNm letModule = hNm `HM.lookup` hNameBinds letModule
localLookup  hNames  = (`HM.lookup` hNames)
moduleLookup _ _ = Nothing
--moduleLookup imports hNm = let
--    lookupNm_Module   nm cm = (,cm) <$> nm `HM.lookup` hNameBinds cm
--  in case asum (lookupNm_Module hNm <$> imports) of
--  Nothing  -> pure Nothing
--  Just (iNm, cm) ->
--    let bind = bindings cm V.! iNm
--        addNm hNm bind = do
--          nm <- freshName
--          addHName hNm nm
--          addLocal nm bind
--    in Just <$> case bind of
--    LClass inf classNm overloads -> -- class, need to import overloads
--      let importTy = importType cm
--          importBind i = do -- TODO update the type
--            let bind = bindings cm V.! i
--            ty <- importTy $ typed (info bind)
--            let bind' = bind{info=(info bind){typed=ty}}
--            freshName >>= (`addLocal` bind')
--          importOverload (iTy , indx)
--            = liftA2 (,) (importTyAlias cm iTy) (importBind indx)
--      in do
--      lookupTyHNm classNm -- add class polytype
--      overloads' <- traverse importOverload $ IM.toList overloads
--      t <- importTy $ typed inf
--      addNm hNm (LClass inf{typed=t} classNm (IM.fromList overloads'))
--    _ -> addNm hNm bind
  --    error "untested support for external bindings"

addTy t = freshTyName >>= (`addLocalTy` t)

importTyAlias :: CoreModule -> ITName -> ToCoreEnv ITName
importTyAlias cm i = let ty = (algData cm V.! i)
  in case named ty of
  Nothing-> freshTyName >>= (`addLocalTy` ty)
  Just n -> lookupTyHNm n <&> \case
     { Just x->x ; Nothing -> error "impossible" }

-- recursively bring in all references to the type
--importType :: CoreModule -> Type -> ToCoreEnv Type
importType cm t = case t of
--  TyAlias i   -> TyAlias <$> importTyAlias cm i
--  TyArrow tys -> TyArrow <$> mapM (importType cm) tys
--  TyPoly (Join tys) ->
--    TyPoly . Join <$>  mapM (importType cm) tys
  t -> pure t

lookupTyHNm hNm = gets hTyNames >>=
  \hs -> case (hs `localTyLookup` hNm) of
  { Nothing->gets imports >>= (`moduleTyLookup` hNm); x->pure x }
localTyLookup hTyNames  = (`HM.lookup` hTyNames)
moduleTyLookup imports hNm = let
    lookupTyNm_Module nm cm = (,cm) <$> nm `HM.lookup` hNameTypes cm
  in case asum (lookupTyNm_Module hNm <$> imports) of
  Nothing  -> pure Nothing
  Just (iNm, cm) -> Just <$> do --importType cm (TyAlias iNm)
    nm <- freshTyName
    addTyHName hNm nm
    addLocalTy nm (algData cm V.! iNm)
