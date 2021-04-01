## Record
* link-time translation to merge module field tables
* Lens allowing treatment as if has less fields
? qtt fields

## Sum = Peano | Flat | Tree | Wrapper Sum

## Fn ; FnPtr = PAp | Raw | Poly
* data/poly args extra frame ptr

??
conv recursion to list function

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
