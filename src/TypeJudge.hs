{-# LANGUAGE GeneralizedNewTypeDeriving #-}
module TypeJudge where
import Core as C

-- Type judgements: checking and inferring
-- The goal is to prepare for codegen
--   * evaluate (static) dependent types
--   * type-check
--   * inference: reduce every type to an llvm.AST.Type
--
-- runtime dependent types ?
--  | add runtime assertions
--  | check all functions are total
--  | do nothing (risk segfaults/weird behavior)

-- the monad for type judgements, it just contains the module
newtype JudgeMonad = JudgeMonad { unJM :: CoreModule)
  deriving (Functor, Alternative, Applicative, Monad, MonadPlus)

instance Applicative JM where
  fmap f (JM mod) = JM (f mod)

judgeModule :: CoreModule -> CoreModule
judgeModule (CoreModule env binds) =
  imapM (judgeBind) binds

-- Judging
-- upwards   is inference
-- downwards is checking
judgeTopBind :: Name -> CoreExpr -> CoreExpr
judgeTopBind nm e =
  let info = env ! nm in
  case typed info of
    TyUnknown -> infer
    TyBoxed t -> infer
    vanilla   -> check
