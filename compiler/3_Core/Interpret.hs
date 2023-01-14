-- Fully inline, β-reduce and constant fold
-- ! may as well do this in FEnv then
module Interpret where
import CoreSyn

interpretModule :: JudgedModule -> Text
interpretModule jm = _
--
--type BetaEnv t = () -- lookup VBruijns , VQBinds , VLetBinds
--type Terminal = Term -- | PrimInstr | BruijnAbs | Tuple | Block
--
--betaReduceF :: Termf -> BetaEnv Terminal
--betaReduceF = \case
--  VarF v -> case v of
--    VQBind   q -> _
--    VLetBind q -> _
--  VBruijnF i   -> _
--  AppF     f args -> _
--  CaseB   scrut retT branches def -> _
--  other -> _
