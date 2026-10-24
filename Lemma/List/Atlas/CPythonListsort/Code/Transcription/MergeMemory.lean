import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Transcription.MergeMemory
open CPythonListsort


namespace CPythonListsort

/--
[mergeDataMemmove_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeDataMemmove_eq
  {site : MergeMemmoveCallsite}
  {data : SortSlice κ ν}
  {dst src : Int}
  {count : Nat} :
-- imply
  mergeDataMemmove? site data dst src count = data.memmove? dst src count :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeDataMemmove_entries_size_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeDataMemmove_entries_size_of_eq_some
  {site : MergeMemmoveCallsite}
  {data updated : SortSlice κ ν}
  {dst src : Int}
  {count : Nat}
-- given
  (h : mergeDataMemmove? site data dst src count = some updated) :
-- imply
  updated.entries.size = data.entries.size :=
-- proof
  SortSlice.memmove_entries_size_of_eq_some data updated dst src count h

end CPythonListsort

namespace CPythonListsort

/--
[mergeFreemem_inline](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeFreemem_inline
  {state : MergeState κ ν}
-- given
  (h : state.a.backing = .inline) :
-- imply
  mergeFreemem state = state := by
-- proof
  simp [mergeFreemem, h]

end CPythonListsort

namespace CPythonListsort

/--
[mergeFreemem_noninline](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeFreemem_noninline
  {state : MergeState κ ν}
-- given
  (h : state.a.backing ≠ .inline) :
-- imply
  (mergeFreemem state).a = { state.a with cells := #[], backing := .released } := by
-- proof
  simp [mergeFreemem, h]

end CPythonListsort

namespace CPythonListsort

/--
[mergeFreemem_tempStorageInv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeFreemem_tempStorageInv
  {state : MergeState κ ν}
-- given
  (hInv : TempStorageInv state.a state.alloced) :
-- imply
  TempStorageInv (mergeFreemem state).a (mergeFreemem state).alloced := by
-- proof
  unfold mergeFreemem
  split
  · simpa using hInv
  · simp [TempStorageInv]

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_reused](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeGetmem_reused
  {state : MergeState κ ν}
  {need : PySSize}
-- given
  (hReuse : need.sle state.alloced = true) :
-- imply
  mergeGetmem state need = { state := state, outcome := .reused } := by
-- proof
  simp [mergeGetmem, hReuse]

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_guardRejected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeGetmem_guardRejected
  {state : MergeState κ ν}
  {need : PySSize}
-- given
  (hReuse : need.sle state.alloced = false)
  (hGuard : mergeGetmemAllocationLimit state.a < need.toNat) :
-- imply
  mergeGetmem state need = { state := mergeFreemem state, outcome := .guardRejected } := by
-- proof
  simp [mergeGetmem, hReuse, hGuard]

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_grown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeGetmem_grown
  {state : MergeState κ ν}
  {need : PySSize}
-- given
  (hReuse : need.sle state.alloced = false)
  (hGuard : need.toNat ≤ mergeGetmemAllocationLimit state.a) :
-- imply
  let result := mergeGetmem state need result.outcome = .grown ∧ result.state.alloced = need ∧ result.state.a.backing = .heap ∧ result.state.a.hasValues = state.a.hasValues ∧ result.state.a.cells = Array.replicate need.toNat none := by
-- proof
  by_cases hInline : state.a.backing = .inline <;>
    simp [mergeGetmem, hReuse, Nat.not_lt.mpr hGuard, mergeFreemem, hInline]

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_grown_physicalSlots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeGetmem_grown_physicalSlots
  {state : MergeState κ ν}
  {need : PySSize}
-- given
  (hReuse : need.sle state.alloced = false)
  (hGuard : need.toNat ≤ mergeGetmemAllocationLimit state.a) :
-- imply
  (mergeGetmem state need).state.a.physicalSlots = state.a.multiplier * need.toNat := by
-- proof
  by_cases hInline : state.a.backing = .inline <;>
    by_cases hValues : state.a.hasValues = true <;>
      simp [mergeGetmem, hReuse, Nat.not_lt.mpr hGuard, mergeFreemem, hInline,
        TempStorage.physicalSlots, TempStorage.multiplier, hValues]

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_atAllocationLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeGetmem_atAllocationLimit
  {state : MergeState κ ν}
  {need : PySSize}
-- given
  (hReuse : need.sle state.alloced = false)
  (hLimit : need.toNat = mergeGetmemAllocationLimit state.a) :
-- imply
  (mergeGetmem state need).outcome = .grown :=
-- proof
(mergeGetmem_grown state need hReuse (by omega)).1

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_onePastAllocationLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeGetmem_onePastAllocationLimit
  {state : MergeState κ ν}
  {need : PySSize}
-- given
  (hReuse : need.sle state.alloced = false)
  (hLimit : need.toNat = mergeGetmemAllocationLimit state.a + 1) :
-- imply
  (mergeGetmem state need).outcome = .guardRejected := by
-- proof
  rw [mergeGetmem_guardRejected state need hReuse (by omega)]

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_keyed_boundary_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeMemory.lean)
-/
@[path]
lemma mergeGetmem_keyed_boundary_regression
  {state : MergeState κ ν}
-- given
  (hValues : state.a.hasValues = true)
  (hGrowth : (((2 ^ 59 - 1 : Nat) : PySSize).sle state.alloced) = false) :
-- imply
  mergeGetmemAllocationLimit state.a = 2 ^ 59 - 1 ∧ (mergeGetmem state ((2 ^ 59 - 1 : Nat) : PySSize)).outcome = .grown ∧ (mergeGetmem state ((2 ^ 59 : Nat) : PySSize)).outcome = .guardRejected := by
-- proof
  have hRejectGrowth : (((2 ^ 59 : Nat) : PySSize).sle state.alloced) = false := by
    simp [BitVec.sle] at hGrowth ⊢
    omega
  have hLimit : mergeGetmemAllocationLimit state.a = 2 ^ 59 - 1 := by
    simp [mergeGetmemAllocationLimit, TempStorage.multiplier, hValues,
      PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  refine ⟨hLimit, ?_, ?_⟩
  · apply mergeGetmem_atAllocationLimit state _ hGrowth
    simp [hLimit]
  · apply mergeGetmem_onePastAllocationLimit state _ hRejectGrowth
    simp [hLimit]

end CPythonListsort


-- created on 2026-10-23
