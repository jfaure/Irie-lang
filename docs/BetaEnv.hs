-- # β-reduction of higher order functions can have exponential amounts of sharing
-- To share computations inside lambdas (partial applications); ! Do not gratuitously duplicate applications

-- # Linearise CoreSyn => App Module (Bindings <> Externs)
-- Convert all Bindings to Args (LiNames): VLocal | VBind | VExtern => LiName
-- This gives lin info on all bindings and externs within the module and prepares the β-reduction

-- # β-Plan
-- 1. At PAp creation, papcreate returns a new simplified PAp
-- 2. Duped lambdas that end up sharing arguments must make PAps on the shared arg

-- * x + y + z has many possible paps to avoid sharing an addition...
-- ? | compile-fold (+ inline higher-order fn args) | interpret | fn entry-point table | sup-args | monomorphize (not scalable)

-- ~ Duped Labels = Stream; lazy fns duped incrementally; write their params to global memory as new Dup-nodes (thunks)
-- Since It's hard to tell how much of it will be needed by all dups nodes

-- # Memory management

-- * derivatives of Sups are also Sups; until dup at the end of dup-lam resolves them
-- * temp dups | sups inserted by reduction rules:
--   1. sub-dups constructor params (if lazy)
--   2. sup lambda arguments (implicitly duped lambda-body)
--   3. App-sub (sup fn) & Strict-App (sup args)
--   4. Dup-Sup-Main (dup each elem of superposition) & mk new superpositions
-- ? cloning Match lambdas (when pass through dup node)

-- Optimisations:
-- Desaturate CaseFn: case-splits not requiring all args should push extra args into each branch (so strict in first n args)
-- Case-of-Label ; Case-of-Case ; general constant-folding
-- Specialise li: 'dynamically' dup input binds: search for matching shapes in LiName specs
--   Just s  -> dup s (an App of duped Li)
--   Nothing -> dup li and make new specialisation
-- If re-specialising: dup the specialisation and beta-reduce
-- Don't erase bindings on last dup because we may spawn more specialisations

-------------
-- Codegen --
-------------
-- Allocator:
-- In: Arg = Dominated?
-- Ip: Duplicated args? partial free dominated args
-- Out: sort free and used mem from args

-- Data:
-- inplaceable = dominated & not duplicated
-- record = ptr list

-- @ Fn-Call: passdown retptr (if cannot return in registers)
-- @ UnCons:
--   1. if Ptr 0 bit set, this points to dup node (ref-counted memory)
--   2. read into registers | erase unused parts
--   3. maybe (if dominated & not duplicated add node to free-list) (? Or rely on fusion)
-- @ Cons:
--   0. if retptr, write to that
--   1. pre-alloc retptrs for sub-data
--     | from existing retptr
--     | merge subdata chunks
--
--   1. try loose-mem (uncommited free-list), since could be inplaceable
--   2. merge subdata Runs and alloc from there (may be shared among threads)
-- @ Dup: lazy clone
-- @ Ret:
--   1. blanket free args (minus shared and returned memory)
--   2. iff ret value contains no subdata from the args
-- @ Era:

RetPtr: arena pre-allocated (or stack memory); Prepared by a Cons containing subdata

! x86 instrs: BT , Test , pdep
? Region -> Run bitMask
? Merge regions
  Sumdatas within sumdatas (chk sz lookup)
? Dups
? Record subtyping
? poly
? cyclic
? dynamic fusion
? record field assign gets bigger
? data Tree = Int ; { Int ; Tree } -- mu-knot is nested; lift to top of structure ?
? Flatten all record structure
  { { x , y } , { a , b} } = { x , y , a , b } => record field assign got bigger
  want to sequence chunks ; linked list ?
? polymorphic functions that rearrange memory
! Tree alloc = keep splitting a run to continue exploiting implicit pointer (alloc schemes)
! Flatten + sort records
? drop bit from record
? sort record fields based on size
? Insert into array/tree

@ Fn
  * lookup µ-binder at fn calls (recursion only happens through fns)
  * tupled with size_t indicating passdown required
  * small structs in registers , large structs in retPtr (if sumtype > 1 alt also BitTag)
  * passdown mem for all flattened records (calculated from polysize args) + BitTag (if sumtypes | poly) + FieldMarks
@ Cons  : retptr => merge arg runs (HeteroList + Runs + record of sizes (run lookup table)
  * Wrap-rec
  * In-rec
@ UnCons: read , erase unused parts , free node
@ Embed : Make new larger BitTag + header to cover all possible alts (? may have to ptr if >regSize)
@ Drop  : Set bit in FieldMarks
@ Insert: iff changes size, Copy whole record.
@ Join  : Copy records
@ Lens  : consult sorted and uniformized list of labels to find offset

-- drop fields & insert (resize) field & inline subrecords
-- ! ret-subtype by passdown of fieldMask (passdown enough mem anyway in case fn needs it)
-- ! byte align fields
-- ! retPtr indicates pre-dropped fields (should check statically if fn benefits from skipping computations)
Record = record
  FieldMarks -- ! Copy is better; (Iff record > 4 regs) 64-bit header indicating bytes skipped over by record sumtyping
  BitTags    -- N x ntags taglist for sumtypes contained within
  userdata

-- * Embed (subtype into larger sumdata) = copy bittags into larger header (run-length encoded ?)
SumData = data
  | Single         -- parameterised by sizes of poly / recursive holes (No need to label until subtype embeds it)
                   -- >0 , start-run = run-size , end has new tag + explicit pointer
                   -- <0 , custom labels
    userdata
  | Recursive
    NextRegion     -- iff same size (iff at run alignment need to check if ok)
    Header         -- (List run + sumdata tags)

Allocator:
NewRetPtr : Sz -> Run
mergeRuns : Run -> Run -> Run
erase     : Arg -> ()

CHUNKSZ = 0x1000000 -- 4MiB
PAGESZ  = 0x1000    -- 4KiB
Run    = { inUseRegions : BitMask , runMerges : [Run] }
Chunk  = { pageMap : PageMeta X (CHUNKSZ / PAGESZ) }
RetPtr = ?

! BLCS = set lowest clear bit
! nthSet : BitSet -> Nat -> Nat = \b n => tzcnt (pdep (1 `shiftL` n) x)
--------------
-- Jemalloc --
--------------
-- Runs always aligned to multiple of page size (0x1000 = 4KiB)
-- 64-bit defaults: small[8] = [16,32,48,..128] , [192,256,320..512], [768,1024,1280..3840]
-- large: [4KiB , 8 , 12 .. 4072] don't fit in page; metadata in chunk
-- Huge: [4MiB , 8 , 12 ..] don't fit in chunk
-- malloc sz = if sz >= arenamax then new_chunk else
--   if size >= Large then new_run else let
--     bin = get_bin sz -- bins have associated size class (multiple runs)
--     run = if notFull bin.runcur then bin.runcur else bin.runcur = lookupOrAlloc_run
--     bit = clz run.mask
--     in getRegion run bit
--
-- free addr = if addr == chunkAddr then unmapHuge addr else
--   let run = addr2Run addr in
--   if smallAlloc addr
--   then unsetBit run.mask (getElemIndex addr run)
--   else let -- large allocation
--     chunk = runChunk run
--     runIdx = getRunIdx run chunk
--     markFreePages runIdx
--     when AllChunkPagesFree (unmapChunkPages chunk)
--
-- new_chunk = -- parent arena ; list & count of dirty chunks ; i8[] map of pages in chunk
-- new_run   = -- parent arena bin ; bitmask for regions in use ; (runSize?)
-- addBin    = -- sizeclass ; current run ; regionsperrun ; tree of runs

-- sizeclass2runsize

type BetaEnv s = StateT (Beta s) (ST s)
data Beta s = Beta {
--   _thisMod     :: IName
-- , _extBinds    :: V.Vector (V.Vector Expr)
-- , _cBinds      :: MV.MVector s Bind
   _linSubs  :: MV.MVector s Term -- dups and superpositions (Lin | Sup) varnames
 , _linCount :: Int
 , _dupEdges :: BitSet -- vv See below
}; makeLenses ''Beta

-- Dup-Edges:
-- 1 0 0 1 1 0
-- [A , B , C] => 1 C , 0 B , 2 A
-- 0's indicate uses of the substitution (none => Erase ; 1 => LiName ; 2+ => Dups)
-- Providing a new LiName pointing to existing node = 4 Bitwise operations on a BigInt:
insert0At de li     = (de `shiftR` li `shiftL` (li + 1)) .|. (de .&. (setNBits li))
liName2SubIdx de li = popCount (de .&. (setNBits (1 + li))) - 1
dupLi li = dupEdges %= (`insert0At` li)

getSubIdx li = use dupEdges <&> \de -> liName2SubIdx de li

setSub :: LiName -> Term -> BetaEnv s ()
setSub li t = getSubIdx li >>= \i -> use linSubs >>= \subs -> MV.write subs i t
getSub li   = getSubIdx li >>= \i -> use linSubs >>= \subs -> MV.read subs i

-- Spawn a new dup node for a Term
dupTerm t n = (linCount <<%= (n+)) >>= \li -> (dupEdges %= (`setBit` li)) *> setSub li t $> li

dup :: Term -> BetaEnv s (Term , Term)
dup t = case t of
  Lin li -> dupLi li $> (Lin li , Lin li)
  t      -> dupTerm t 2 <&> \li -> (Lin li , Lin (1 + li))

-- constant / predictable dup count ?
-- free dupnode on last read?
-}
