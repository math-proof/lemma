/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean -/

import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.MergeMovementCorrectness
/-!
# Exact semantics of merge movement primitives

The safety layer proves that merge reads and writes stay within their allocated
backings.  Functional merge proofs additionally need the exact whole-entry
effect of those movements.  This module records that effect against the input
snapshot: a successful movement copies each key/payload pair from its original
source position and changes no position outside its destination range.

The signed, pointwise predicates below match the pointer-shaped transcription.
Natural-indexed `SortSlice.EqualOutsideRange` consequences are supplied for
the range-facing correctness layer.
-/


namespace CPythonListsort

universe u v

variable {kappa : Type u} {nu : Type v}

namespace SortSlice

/-- Exact content frame for a natural-indexed temporary destination range. -/
structure ReadFrameNat (before after : TempStorage kappa nu)
    (dst count : Nat) : Prop where
  cellsSize : before.cells.size = after.cells.size
  backing : before.backing = after.backing
  hasValues : before.hasValues = after.hasValues
  read_eq : ∀ index, index < dst ∨ dst + count ≤ index →
    mergeLoTempRead? after index = mergeLoTempRead? before index

/-- Exact content frame for a signed-indexed temporary destination range. -/
structure ReadFrameInt (before after : TempStorage kappa nu)
    (dst : Int) (count : Nat) : Prop where
  cellsSize : before.cells.size = after.cells.size
  backing : before.backing = after.backing
  hasValues : before.hasValues = after.hasValues
  read_eq : ∀ index, index < dst ∨ dst + Int.ofNat count ≤ index →
    mergeHiTempRead? after index = mergeHiTempRead? before index

end SortSlice
end CPythonListsort
