// Rank 1 splitter
// foldr f start = \case of { Next x xs => f x (foldr f start xs) ; Null => start }
// Eagerly splits from the depths
// foldr = rawST [
//   f x (foldr f start xs) -- splitting an inner label; lift to top level; needs access to generator
//   const start
//   ]

