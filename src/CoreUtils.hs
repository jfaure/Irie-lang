-- CoreUtils: pretty printing core

module CoreUtils where

--import CoreSyn

--ppCoreModule :: CoreModule -> IO ()
--ppCoreModule m = ppCoreExpr <$> topBinds m
--
--ppCoreExpr :: CoreExpr -> IO ()
--ppCoreExpr (Var n) = print n
--ppCoreExpr (Lit l) = print l
--ppCoreExpr (App a b) = ppCoreExpr a
--                     *> print "(" *> ppCoreExpr b *> print ")"
