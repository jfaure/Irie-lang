# Goals
Maximise tail call potential

??
Identify hylomorphisms
Data extraction
fields qtt

## Record
* link-time translation to merge module field tables
* Lens allowing treatment as if has less fields

Record =
 | Struct
 | PtrTable

## SumKind = let S = Peano | Flat | Tree in S | Wrapper S
 * Modify Shared subtrees
   1. have to leave marker label at node that is usually ignored
   2. fns to handle shares used by non-master data that don't ignore marker

## FnPtr = PAp | Raw
* use spare bits in pointer alignment to tell pap from rawPtr
* data/poly args extra frame ptr (have to trust local bitcasts)

## Algorithm
Abs:
  dataArgs come with framePtr
App:
  dup args if needed by fn
  (maybe) end the retframe builder
Label: like App, also
  merge data arg frames (or make a frame)
  either newFrag, or (flat data) pushFrag
Match:
  insert extra dups on each branch; report min for whole branch
  register split data (basically inline the splitter fns)
  if frame not used: free frame else free frags (if marked as useful to do so)

## Allocator api
mergeFrames : [Frames] -> Frame
shareFrame : Int -> Frame -> Frame
freeFrame : Frame -> ()

newFrag : Frame -> Size -> Frag
freeFrag : Frame -> Frag -> Size -> ()
dflist_mergeframes : [Frames] -> Frame
push : Frame -> Size -> Frag
pop  : Frame -> Size -> ()
