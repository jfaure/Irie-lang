module Name where

--atm. VLetName = let-depth bound (index into bindings table)

-- lookup mutually in scope modules (esp. imports)
newtype UpName = UpName Word64 -- (Depth , Mod , IName)
upNameDepth (UpName n) = n `shiftR` 48
upNameMod   (UpName n) = (n `shiftR` 32) .&. 0xFFFFFFFF
upNameIName (UpName n) = n .&. 0xFFFFFFFF
mkUpName depth mod i = UpName $ depth `shiftL` 48 .|. (mod `shiftL` 32) .|. i

-- Lens into modules
-- QName is a 2layer DownName from global module map
newtype DownName = DownName [Word16]
