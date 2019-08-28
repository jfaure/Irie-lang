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

-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TypeJudge where
import CoreSyn as C

import Data.Vector
import qualified Data.Map as M
import Control.Monad
import Control.Applicative

--judgeModule :: CoreModule -> CoreModule
--judgeModule (CoreModule env binds) =
--  imapM judgeBind binds
--
-- Judging
-- upwards   is inference
-- downwards is checking
--judgeTopBind :: Name -> CoreExpr -> CoreExpr
--judgeTopBind nm e =
--  let info = env ! nm in
--  case typed info of
--    TyUnknown -> infer
--    TyBoxed t -> infer
--    vanillaTy -> check vanillaTy
