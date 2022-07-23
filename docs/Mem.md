# Record of Sumtype
  * Sort and align to the byte.
  * poly sizes are known to functions as arguments
  BitTags   -- N x ntags taglist for sumtypes (min info to encode a type)
            -- + 1 bit iff boxed field => read pointer
  FieldTags -- Bytes skipped over (0-64 bytes) (more if record is bigger); byte align
  UserData

# Recursive -- data tree + tag tree. (! Split elems into separate lists for simd purposes)
  NextRegion : Ptr -- Elems all eq size
  Header
    Runs    : N x Ptr -- One for each sumtype alt
    RecTags : [Alt , Int] -- run-length encoding of tags

# RetPtr (may be larger or smaller than required)
  smaller: markers for pre-subtying on fields
  larger:  building a part of the record

# StackFrame (mem belongs to all sub-stack frames, shared accross threads)
  free-list of non-recursive memory

@ Fn
  * getRetMem: check free stackMem
  * rec type iff any label is contained again
  * tuple with size_t passdown required in case poly function
  * small structs in registers , large in retPtr
@ Cons (merge args)
  Rec =>
@ UnCons =>
@ EmbedSumtype
@ Join   => copy
@ Lens (Drop as special case of .= ()) => size changing operation need to update upstream fieldtags

# Static
## Record of sumtype
1. Flatten all record structure
2. sort record fields on size
3. Add poly parameters
4. tighten sumtype wraps
5. Extract non-recursive sum-tags from rec structures
* pointer indirection for large sumtype alts
## BitTags
* minimum info necessary to encode an alt

? cyclic
? pre-dropped fields
? dups
? dynamic fusion
? irregular branches (eg List + Tree in sumtype)
? case-out some sum-alts
? read-only dups
perf improvements also help floating point precision
cache line size aligned 64 bytes
