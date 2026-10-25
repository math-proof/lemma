/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Def.CPythonListsort.Code.Transcription.MergeAt.Part2
/-!
# Pending-stack merge dispatch

This module transcribes CPython's `merge_at`.  The pending-stack replacement
happens before either galloping search, exactly as it does in C, so a later
modeled failure retains that mutation.  The two searches trim entries already
in their final positions and the shorter remaining run selects `merge_lo` or
`merge_hi`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- The exact source values retained at a post-trimming merge call site.  The
original selected runs and both gallop results are intentionally retained so
assembly proofs can connect trimming monotonicity to the gallop safety
theorems rather than to the defensive checks in `prepareMergeAt?`. -/
structure MergeAtCall (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  ssa : Int
  ssb : Int
  na : Nat
  nb : Nat
  left : PendingRun
  right : PendingRun
  firstB : SortSliceEntry κ ν
  lastA : SortSliceEntry κ ν
  trimA : GallopResult
  trimB : GallopResult

end CPythonListsort
