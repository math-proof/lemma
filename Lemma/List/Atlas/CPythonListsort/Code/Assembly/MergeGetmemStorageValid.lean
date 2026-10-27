import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
open CPythonListsort CPythonListsort.MergeGetmemStoragePost


namespace CPythonListsort

/--
[TempStorageInv.physicalSlots_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma TempStorageInv.physicalSlots_eq
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {alloced : PySSize}
-- given
  (hInv : TempStorageInv storage alloced)
  (hLive : storage.Live) :
-- imply
  storage.physicalSlots = storage.multiplier * alloced.toNat := by
-- proof
  rw [TempStorage.physicalSlots, TempStorageInv.cells_size_eq hInv hLive]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[toNat_le_of_sle_of_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
capacity when viewed as a natural number.  The signed comparison itself forces
the larger word to be nonnegative as well. -/
private lemma toNat_le_of_sle_of_nonnegative
  {need capacity : PySSize} (hNeed : need.Nonnegative)
  (hReuse : need.sle capacity = true) :
  need.toNat ≤ capacity.toNat := by
  have hSigned : need.toInt ≤ capacity.toInt := by
    simpa [BitVec.sle] using hReuse
  have hCapacity : capacity.msb = false := by
    by_contra hNegative
    have hCapacityTrue : capacity.msb = true :=
      Bool.eq_true_of_not_eq_false hNegative
    have hNeedNonnegative := BitVec.toInt_nonneg_of_msb_false hNeed
    have hCapacityNegative := BitVec.toInt_neg_of_msb_true hCapacityTrue
    omega
  rw [BitVec.toInt_eq_toNat_of_msb hNeed,
    BitVec.toInt_eq_toNat_of_msb hCapacity] at hSigned
  exact_mod_cast hSigned

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[physicalSlots_le_of_allocationLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
fresh allocation.  `multiplier` is definitionally one or two. -/
private lemma physicalSlots_le_of_allocationLimit
  (storage : TempStorage κ ν) (need : PySSize)
  (hLimit : need.toNat ≤ mergeGetmemAllocationLimit storage) :
  storage.multiplier * need.toNat ≤
    PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
  cases hValues : storage.hasValues <;>
    simp only [mergeGetmemAllocationLimit, TempStorage.multiplier, hValues,
      Bool.false_eq_true, ↓reduceIte] at hLimit ⊢
  · simpa using hLimit
  · have hMul :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hLimit
    simpa [Nat.mul_comm] using hMul

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_growth_intermediate_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma mergeGetmem_growth_intermediate_free
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
-- given
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live) :
-- imply
  MergeGetmemIntermediateFree state (mergeFreemem state) := by
-- proof
  refine
    { exactState := rfl
      invariant := mergeFreemem_tempStorageInv state hInv
      allocedPreserved := ?_
      valuesModePreserved := ?_
      backingTransition := ?_ }
  · simp [mergeFreemem]
    split <;> rfl
  · simp only [mergeFreemem]
    split <;> rfl
  · cases hBacking : state.a.backing with
    | inline =>
      left
      simp [hBacking]
    | heap =>
      right
      simp [mergeFreemem, hBacking]
    | released =>
      exact (hLive hBacking).elim

end CPythonListsort

namespace CPythonListsort

/--
[mergeFreemem_nonStorageFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma mergeFreemem_nonStorageFrame
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  (mergeFreemem state).mergeGetmemNonStorageFrame = state.mergeGetmemNonStorageFrame := by
-- proof
  unfold mergeFreemem
  split <;> rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_nonStorageFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma mergeGetmem_nonStorageFrame
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {need : PySSize} :
-- imply
  (mergeGetmem state need).state.mergeGetmemNonStorageFrame = state.mergeGetmemNonStorageFrame := by
-- proof
  unfold mergeGetmem
  split
  · rfl
  · dsimp only
    split
    · exact mergeFreemem_nonStorageFrame state
    · simpa only [MergeState.mergeGetmemNonStorageFrame] using
      mergeFreemem_nonStorageFrame state

end CPythonListsort

namespace CPythonListsort.MergeGetmemStoragePost

/--
[listlen_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma listlen_eq
  {κ : Type u}
  {ν : Type v}
  {before : MergeState κ ν}
  {need : PySSize}
-- given
  (h : MergeGetmemStoragePost before need result) :
-- imply
  result.state.listlen = before.listlen :=
-- proof
  congrArg MergeGetmemNonStorageFrame.listlen h.nonStorageFrame

end CPythonListsort.MergeGetmemStoragePost

namespace CPythonListsort.MergeGetmemStoragePost

/--
[basekeys_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma basekeys_eq
  {κ : Type u}
  {ν : Type v}
  {before : MergeState κ ν}
  {need : PySSize}
-- given
  (h : MergeGetmemStoragePost before need result) :
-- imply
  result.state.basekeys = before.basekeys :=
-- proof
  congrArg MergeGetmemNonStorageFrame.basekeys h.nonStorageFrame

end CPythonListsort.MergeGetmemStoragePost

namespace CPythonListsort.MergeGetmemStoragePost

/--
[data_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma data_eq
  {κ : Type u}
  {ν : Type v}
  {before : MergeState κ ν}
  {need : PySSize}
-- given
  (h : MergeGetmemStoragePost before need result) :
-- imply
  result.state.data = before.data :=
-- proof
  congrArg MergeGetmemNonStorageFrame.data h.nonStorageFrame

end CPythonListsort.MergeGetmemStoragePost

namespace CPythonListsort.MergeGetmemStoragePost

/--
[pending_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma pending_eq
  {κ : Type u}
  {ν : Type v}
  {before : MergeState κ ν}
  {need : PySSize}
-- given
  (h : MergeGetmemStoragePost before need result) :
-- imply
  result.state.pending = before.pending :=
-- proof
  congrArg MergeGetmemNonStorageFrame.pending h.nonStorageFrame

end CPythonListsort.MergeGetmemStoragePost

namespace CPythonListsort.MergeGetmemStoragePost

/--
[minGallop_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma minGallop_eq
  {κ : Type u}
  {ν : Type v}
  {before : MergeState κ ν}
  {need : PySSize}
-- given
  (h : MergeGetmemStoragePost before need result) :
-- imply
  result.state.min_gallop = before.min_gallop :=
-- proof
  congrArg MergeGetmemNonStorageFrame.min_gallop h.nonStorageFrame

end CPythonListsort.MergeGetmemStoragePost

namespace CPythonListsort.MergeGetmemStoragePost

/--
[keyCompare_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma keyCompare_eq
  {κ : Type u}
  {ν : Type v}
  {before : MergeState κ ν}
  {need : PySSize}
-- given
  (h : MergeGetmemStoragePost before need result) :
-- imply
  result.state.key_compare = before.key_compare :=
-- proof
  congrArg MergeGetmemNonStorageFrame.key_compare h.nonStorageFrame

end CPythonListsort.MergeGetmemStoragePost

namespace CPythonListsort.MergeGetmemStoragePost

/--
[minrun_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma minrun_eq
  {κ : Type u}
  {ν : Type v}
  {before : MergeState κ ν}
  {need : PySSize}
-- given
  (h : MergeGetmemStoragePost before need result) :
-- imply
  result.state.mr_current = before.mr_current ∧ result.state.mr_e = before.mr_e ∧ result.state.mr_mask = before.mr_mask :=
-- proof
  ⟨congrArg MergeGetmemNonStorageFrame.mr_current h.nonStorageFrame,
    congrArg MergeGetmemNonStorageFrame.mr_e h.nonStorageFrame,
    congrArg MergeGetmemNonStorageFrame.mr_mask h.nonStorageFrame⟩

end CPythonListsort.MergeGetmemStoragePost

namespace CPythonListsort

/--
[mergeGetmem_reused_storage_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma mergeGetmem_reused_storage_valid
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {need : PySSize}
-- given
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hNeed : need.Nonnegative)
  (hReuse : need.sle state.alloced = true) :
-- imply
  let result := mergeGetmem state need result.state = state ∧ result.outcome = .reused ∧ MergeGetmemStoragePost state need result := by
-- proof
  rw [mergeGetmem_reused state need hReuse]
  refine ⟨rfl, rfl, ?_⟩
  refine
    { outcome := Or.inl rfl
      live := hLive
      invariant := hInv
      valuesMode := rfl
      nonStorageFrame := rfl
      logicalCapacity := TempStorageInv.cells_size_eq hInv hLive
      requestFits := toNat_le_of_sle_of_nonnegative hNeed hReuse
      physicalSlots := hInv.physicalSlots_eq hLive
      reuseAccounting := fun _ => rfl
      growthIntermediateFree := ?_
      growthAccounting := ?_ }
  · simp
  simp

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_grown_storage_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma mergeGetmem_grown_storage_valid
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {need : PySSize}
-- given
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hNeed : need.Nonnegative)
  (hGrowth : need.sle state.alloced = false)
  (hLimit : need.toNat ≤ mergeGetmemAllocationLimit state.a) :
-- imply
  let result := mergeGetmem state need result.outcome = .grown ∧ result.state.alloced = need ∧ result.state.a.backing = .heap ∧ result.state.a.cells.size = need.toNat ∧ result.state.a.physicalSlots = state.a.multiplier * need.toNat ∧ result.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES ∧ result.state.alloced.Nonnegative ∧ MergeGetmemIntermediateFree state (mergeFreemem state) ∧ MergeGetmemStoragePost state need result := by
-- proof
  have hIntermediate := mergeGetmem_growth_intermediate_free state hInv hLive
  have hGrown := mergeGetmem_grown state need hGrowth hLimit
  have hPhysical := mergeGetmem_grown_physicalSlots state need hGrowth hLimit
  have hPhysicalBound := physicalSlots_le_of_allocationLimit state.a need hLimit
  rcases hGrown with
    ⟨hOutcome, hAlloced, hBacking, hValues, hCells⟩
  have hLiveResult : (mergeGetmem state need).state.a.Live := by
    simp [TempStorage.Live, hBacking]
  have hInvResult :
    TempStorageInv (mergeGetmem state need).state.a
      (mergeGetmem state need).state.alloced := by
    rw [hAlloced]
    simp [TempStorageInv, hBacking, hCells, hValues,
      TempStorage.physicalSlots, TempStorage.multiplier]
  have hLogical :
    (mergeGetmem state need).state.a.cells.size =
      (mergeGetmem state need).state.alloced.toNat := by
    rw [hCells, hAlloced]
    simp
  have hMultiplier :
    (mergeGetmem state need).state.a.multiplier = state.a.multiplier := by
    simp [TempStorage.multiplier, hValues]
  have hBound :
    (mergeGetmem state need).state.a.physicalSlots ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
    rwa [hPhysical]
  refine
    ⟨hOutcome, hAlloced, hBacking, ?_, hPhysical, hBound, ?_, hIntermediate, ?_⟩
  · rw [hCells]
    simp
  · simpa only [hAlloced] using hNeed
  · refine
    { outcome := Or.inr hOutcome
      live := hLiveResult
      invariant := hInvResult
      valuesMode := hValues
      nonStorageFrame := mergeGetmem_nonStorageFrame state need
      logicalCapacity := hLogical
      requestFits := ?_
      physicalSlots := hInvResult.physicalSlots_eq hLiveResult
      reuseAccounting := ?_
      growthIntermediateFree := ?_
      growthAccounting := ?_ }
    · rw [hAlloced]
    · intro hReused
      simp [hOutcome] at hReused
    · intro _
      exact hIntermediate
    · intro _
      exact ⟨hAlloced, hBacking, hMultiplier, hPhysical, hBound⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_storage_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma mergeGetmem_storage_valid
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {need : PySSize}
-- given
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hNeed : need.Nonnegative)
  (hLimit : need.sle state.alloced = false → need.toNat ≤ mergeGetmemAllocationLimit state.a) :
-- imply
  MergeGetmemStoragePost state need (mergeGetmem state need) := by
-- proof
  by_cases hReuse : need.sle state.alloced = true
  · exact (mergeGetmem_reused_storage_valid state need hInv hLive hNeed hReuse).2.2
  · have hGrowth : need.sle state.alloced = false := by
    cases hComparison : need.sle state.alloced
    · rfl
    · exact (hReuse hComparison).elim
    exact
      (mergeGetmem_grown_storage_valid state need hInv hLive hNeed hGrowth
        (hLimit hGrowth)).2.2.2.2.2.2.2.2

end CPythonListsort

namespace CPythonListsort

/--
[releasedTempStorage_not_live](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma releasedTempStorage_not_live
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
-- given
  (hReleased : storage.backing = .released) :
-- imply
  ¬ storage.Live := by
-- proof
  simp [TempStorage.Live, hReleased]

end CPythonListsort

namespace CPythonListsort

/--
[fabricatedStaleReleasedMergeState_reuses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemStorageValid.lean)
-/
@[path]
lemma fabricatedStaleReleasedMergeState_reuses
  {κ : Type u}
  {ν : Type v} :
-- imply
  let state := fabricatedStaleReleasedMergeState let need : PySSize := 4 TempStorageInv state.a state.alloced ∧ ¬ state.a.Live ∧ need.sle state.alloced = true ∧ (mergeGetmem state need).outcome = .reused ∧ (mergeGetmem state need).state = state ∧ (mergeGetmem state need).state.a.backing = .released := by
-- proof
  simp [fabricatedStaleReleasedMergeState, TempStorageInv, TempStorage.Live,
    mergeGetmem]

end CPythonListsort


-- created on 2026-10-23
