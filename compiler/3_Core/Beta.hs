module Beta where
{-
import BetaEnv
import CoreSyn
import ShowCore()
import qualified Data.Vector.Mutable as MV
import qualified Data.Vector as V
import Control.Lens

betaReduceTop :: Int -> Term -> Term
betaReduceTop liCount term = runST $ do
  lins <- MV.generate liCount Lin
  betaReduce term `evalStateT` Beta
    { _linSubs = lins
    }

-- Here we need to inspect values
brApp :: Term -> [Term] -> BetaEnv s Term
brApp f args = case f of
  -- (λx(body) arg) => x <- arg in body
  Abs ars free body ty -> zipWithM_ (\(i,_) t -> sub i t) ars args *> betaReduce body

  -- ({a b} c) => dup x0 x1 = c in {(a x0) (b x1)}
  Sup f g -> (dup `mapM` args) >>= \dups -> let (fArgs , gArgs) = unzip dups
    in betaReduce (Sup (App f fArgs) (App g gArgs))

  -- (+ {a0 a1} b) => dup b0 b1 = b in {(+ a0 b0) (+ a1 b1)}
  f -> do -- Instr | Match | Cast | TTLens
    apps <- elimSupArgs f args    -- A superposition of apps
    pure (SupN (rewriteApp <$> apps)) -- one-step simplification rules

-- Make a sup App for each sup arg
-- (+ {a0 a1} b) => dup b0 b1 = b in {(+ a0 b0) (+ a1 b1)}
elimSupArgs :: Term -> [Term] -> BetaEnv s [Term]
elimSupArgs f args = _

rewriteApp (App f args) = case f of
--Match ty branches d | [scrut] <- args -> fuseMatch ty scrut branches d
  _ -> App f args

-- When inspecting dups, need to evaluate them upto a constructor
solveDup :: LiName -> LiName -> Term -> BetaEnv s ()
solveDup a b term = void $ case term of
  -- Dup-Label: dup all params & re-label the 2 lists
  -- dup x y = (Foo a b ...) => dup a0 a1 = a ; dup b0 b1 = b ... in x <- (Foo a0 b0 ...) ; y <- (Foo a1 b1 ...)
  Label l params -> (dup `mapM` params) >>= \dups -> let
    (p1 , p2) = unzip dups
    in sub a (Label l p1) *> sub b (Label l p2)

  -- Dup-Lam: sub lambda-bounds with sups then Dup the body (requires reflection)
  -- dup a b = λx(body) => a <- λx0(b0) ; b <- λx1(b1) ; x <- {x0 x1} in dup b0 b1 = body
  Abs ars 0 body ty -> do
    args <- (dup . Lin . fst) `mapM` ars
--  free <- dup               `mapM` freeArgs
    zipWithM (\(i,_) (a1,a2) -> sub i (Sup a1 a2)) ars args
    (b1 , b2) <- dup body
    let (a1 , a2) = unzip args
        argTys = snd <$> ars
        (names1 , names2) = ([0..] , [0..]) -- TODO find LiNames for DupPtrs!
    sub a (Abs (zip names1 argTys) emptyBitSet b1 ty)
    sub b (Abs (zip names2 argTys) emptyBitSet b2 ty)
  Abs ars free body ty -> _

 -- dup a b = {r s} => a <- r ; b <- s
 -- dup x y = {a b} => x <- {xA xB} ; y <- {yA yB} ; dup xA yA = a ; dup xB yB = b
  Sup x y
   | True -> sub a x *> sub b y -- Dup-Sup-Lam (lambda body duplication)
   | otherwise -> do            -- Dup-Sup anything else
    (a1 , a2) <- dup x
    (b1 , b2) <- dup y
    sub a (Sup a1 a2) *> sub b (Sup b1 b2)

  -- dup-copy: copy the literal
  t -> sub a t *> sub b t

betaReduce :: Term -> BetaEnv s Term
betaReduce t = case t of
  Lin li -> getSub li     -- inlining
  Sup li -> pure (Sup li) -- uninspected sups left as is

  App f args -> brApp f args
  Abs ars free t ty -> betaReduce t <&> \t' -> Abs ars free t' ty

  -- recurse into all branches
  Cons fields -> Cons <$> (betaReduce `traverse` fields)
  TTLens record lens op -> _
  Label l params -> Label l <$> (betaReduce `traverse` params)
  Match ty branches d -> Match ty
    <$> (betaReduce `traverse` branches)
    <*> (maybe (pure Nothing) (fmap Just . betaReduce))
  Cast c a -> Cast c <$> betaReduce a

  -- non-recursive
  Lit{}    -> pure t
  Instr{}  -> pure t
  Poison{} -> pure t
  _ -> error $ show t
-}
