BiCasts =
 | recordTree -- define records recursively

Fn =
  | PAP [args] -- any papped fn needs a papapper fn that reads args from memory
  | sret (ie. data)
  | TyCon Fn -- arg bicasts

? arg stack levels (ie. lifetime)
? dupped args

# Callers
* Args marked in ret are OK up a single Frame
* Constants aren't functions (no sret)
call =
 (sv | exec) tycon casts
 when sret and any inRet args;
   data returned by fns with local inRet args must be copied to sret

SRet : { i32 ; .. } =
 | None
 | PreCast IntSet (bitmask of which indexes should be dropped)

Lazy tycon casts; subdata

# Fn Args
 * InRet if arg >life ret then _ else copy arg
 * Writeable ; have to copy it at the callsite if shared

# record Rets
 * Constants: emit as constant (+ subtyper function (generally needed))
 * mk        : rect = { a = 3 ; b = 2 }
 * & takeArg : write an arg tycon into the ret (this requires copy if ret outlives arg)
 | - preCast : rec => smaller rec (also avoids calculating unneeded fields)
 | = over    : write in place (if ok?)
 | + cons    : add records together

 * + sort both records into sret
 * = when sret==arg , can avoid copying fields
 * - don't write all fields (*sret == bitmask)
 * argBase reusable iff sret == arg (implies arg >life ret)
? support passing larger srets than expected (probably iff no field interleaving)
sret = { A , B (Unused space for later appends) , C } -- messy
 => A sz += sizeof B | C addr += sizeof B

# Record Args
 * == sret => avoid copying untouched fields
 * field is pointer
 * is shared (partially shared?) => mem unavailable to callees
 * InRetArg =
   | originFrame (if > ret life, can avoid copy)

? returned leaf bicasts when field size changes
? dynamic sret

RecordArg =
 | Struct : { types } -- need copy when dropping centre fields

-- | ptrList: [Ptr] -- extra indirection
-- | SubRecord : { Mask , Struct } -- how to indicate size of dropped fields ?
-- | Record : [Off]      -- prefix sum of offsets
-- | LeafCast : [{i , castFn}] Record

# Free heap record fields (gmp + recursive data)
 * auto generate a LensOver with free function
