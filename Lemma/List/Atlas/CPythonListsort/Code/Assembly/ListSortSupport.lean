import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Assembly.ListSortSupport
open CPythonListsort


namespace CPythonListsort

/--
[listSizeWord_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma listSizeWord_nonnegative
  {κ : Type u}
  {ν : Type v}
  {size : Nat}
-- given
  (hsize : size ≤ PY_LIST_MAX) :
-- imply
  PySSize.Nonnegative (BitVec.ofNat 64 size) := by
-- proof
  rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
  rw [listSizeWord_toNat hsize]
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hsize ⊢
  omega

end CPythonListsort

namespace CPythonListsort

/--
[pySSize_slt_eq_nat_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma pySSize_slt_eq_nat_lt
  {κ : Type u}
  {ν : Type v}
  {x y : PySSize}
-- given
  (hx : x.Nonnegative)
  (hy : y.Nonnegative) :
-- imply
  x.slt y = decide (x.toNat < y.toNat) := by
-- proof
  rw [BitVec.slt_eq_decide]
  rw [BitVec.toInt_eq_toNat_of_msb hx]
  rw [BitVec.toInt_eq_toNat_of_msb hy]
  norm_cast

end CPythonListsort

namespace CPythonListsort

/--
[pySSize_nonnegative_of_toNat_le_maxMinrun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma pySSize_nonnegative_of_toNat_le_maxMinrun
  {κ : Type u}
  {ν : Type v}
  {x : PySSize}
-- given
  (hx : x.toNat ≤ MAX_MINRUN.toNat) :
-- imply
  x.Nonnegative := by
-- proof
  rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
  have hMaxMinrun : MAX_MINRUN.toNat = 64 := by decide
  rw [hMaxMinrun] at hx
  norm_num
  omega

end CPythonListsort

namespace CPythonListsort

/--
[initialMergeState_package](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma initialMergeState_package
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : SortSlice κ ν}
-- given
  (hasKeyfunc : Bool)
  (hsize : input.entries.size ≤ PY_LIST_MAX)
  (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
-- imply
  InitialMergeStatePackage lt hasKeyfunc input (initialMergeState lt hasKeyfunc input).1 := by
-- proof
  let listWord : PySSize := BitVec.ofNat 64 input.entries.size
  have hword : listWord.toNat = input.entries.size :=
    listSizeWord_toNat hsize
  have hnonnegative : listWord.Nonnegative :=
    listSizeWord_nonnegative hsize
  have hwordMax : listWord.toNat ≤ PY_LIST_MAX := by
    simpa [hword] using hsize
  have htempInv := mergeInitTemp_inv (κ := κ) (ν := ν) listWord hasKeyfunc
    hwordMax
  have htempLive :
    (mergeInitTemp (κ := κ) (ν := ν) listWord hasKeyfunc).storage.Live := by
    simp [mergeInitTemp, TempStorage.Live]
  have hstopped := minrunInit_stops_and_exponent_lt_64 listWord hnonnegative
    hwordMax
  refine
    { exactState := rfl
      listlenRoundtrip := ?_
      listlenNonnegative := ?_
      basekeys := ?_
      data := ?_
      pending := ?_
      pendingLayout := ?_
      poweredPrefix := ?_
      tempInvariant := ?_
      tempLive := ?_
      logicalCapacity := ?_
      physicalSlotsBound := ?_
      hasValues := ?_
      valuesMode := ?_
      comparator := ?_
      minrunState := ?_
      minrunStopped := ?_ }
  · simpa [initialMergeState, minrunInitTraced, listWord] using hword
  · simpa [initialMergeState, minrunInitTraced, listWord] using hnonnegative
  · simp [initialMergeState]
  · simp [initialMergeState]
  · simp [initialMergeState]
  · simp [PendingLayout, PendingRunsCover, initialMergeState,
    minrunInitTraced, listWord, hword, hnonnegative]
  · simp [PoweredPrefix, initialMergeState]
  · simpa [initialMergeState, listWord] using htempInv
  · simpa [initialMergeState, listWord] using htempLive
  · exact TempStorageInv.cells_size_eq
    (by simpa [initialMergeState, listWord] using htempInv)
    (by simpa [initialMergeState, listWord] using htempLive)
  · let initialized :=
    mergeInitTemp (κ := κ) (ν := ν) listWord hasKeyfunc
    have hinline : initialized.storage.backing = .inline := by
      simp [initialized, mergeInitTemp]
    have hinitializedInv :
      TempStorageInv initialized.storage initialized.alloced := by
      simpa [initialized] using htempInv
    have hinlineInv :
      initialized.storage.cells.size = initialized.alloced.toNat ∧
        initialized.storage.multiplier * initialized.alloced.toNat ≤
          MERGESTATE_TEMP_SIZE := by
      simpa only [TempStorageInv, hinline] using hinitializedInv
    have hslots :
      initialized.storage.physicalSlots ≤ MERGESTATE_TEMP_SIZE := by
      rwa [TempStorage.physicalSlots, hinlineInv.1]
    have hplatform :
      MERGESTATE_TEMP_SIZE ≤
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
      norm_num [MERGESTATE_TEMP_SIZE, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
    simpa [initialMergeState, listWord, initialized] using
      hslots.trans hplatform
  · simp [initialMergeState, mergeInitTemp]
  · simpa [initialMergeState, mergeInitTemp] using hMode
  · simp [initialMergeState]
  · simp [initialMergeState, MergeState.minrunState, minrunInit,
    minrunInitTraced]
  · simpa [initialMergeState, listWord] using hstopped.1

end CPythonListsort

namespace CPythonListsort

/--
[minrunNextN_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma minrunNextN_add
  {κ : Type u}
  {ν : Type v}
  {first later : Nat}
  {state : MinrunState} :
-- imply
  let prior := minrunNextN first state let suffix := minrunNextN later prior.state (minrunNextN (first + later) state).state = suffix.state ∧ (minrunNextN (first + later) state).outputs = prior.outputs ++ suffix.outputs ∧ (minrunNextN (first + later) state).assertionsPassed = (prior.assertionsPassed && suffix.assertionsPassed) := by
-- proof
  induction first generalizing state with
  | zero => simp [minrunNextN]
  | succ first ih =>
    simp only [Nat.succ_add, minrunNextN]
    let next := minrunNext state
    obtain ⟨hstate, houtputs, hassertions⟩ := ih next.state
    refine ⟨hstate, ?_, ?_⟩
    · simpa only [next, List.cons_append] using
      congrArg (fun outputs => next.result.toNat :: outputs) houtputs
    · change
      (next.assertionPassed &&
        (minrunNextN (first + later) next.state).assertionsPassed) = _
      rw [hassertions]
      exact (Bool.and_assoc _ _ _).symm

end CPythonListsort

namespace CPythonListsort

/--
[minrunNextN_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma minrunNextN_succ
  {κ : Type u}
  {ν : Type v}
  {calls : Nat}
  {state : MinrunState} :
-- imply
  let prior := minrunNextN calls state let next := minrunNext prior.state (minrunNextN (calls + 1) state).state = next.state ∧ (minrunNextN (calls + 1) state).outputs = prior.outputs ++ [next.result.toNat] ∧ (minrunNextN (calls + 1) state).assertionsPassed = (prior.assertionsPassed && next.assertionPassed) := by
-- proof
  simpa [minrunNextN] using minrunNextN_add calls 1 state

end CPythonListsort

namespace CPythonListsort

/--
[adaptiveMinrunScanInvariant_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma adaptiveMinrunScanInvariant_initial
  {κ : Type u}
  {ν : Type v}
  {listSize : PySSize}
-- given
  (hNonnegative : listSize.Nonnegative)
  (hMax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  AdaptiveMinrunScanInvariant listSize 0 0 (minrunInit listSize) := by
-- proof
  constructor
  · exact hNonnegative
  · exact hMax
  · rfl
  · simp [minrunNextN]
  · simp

end CPythonListsort

namespace CPythonListsort

/--
[adaptiveMinrun_step_facts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma adaptiveMinrun_step_facts
  {κ : Type u}
  {ν : Type v}
  {listSize : PySSize}
  {calls scanned : Nat}
  {state : MinrunState}
-- given
  (hInv : AdaptiveMinrunScanInvariant listSize calls scanned state)
  (hActive : scanned < listSize.toNat) :
-- imply
  AdaptiveMinrunStepFacts listSize calls scanned state := by
-- proof
  let prior := minrunNextN calls (minrunInit listSize)
  have hstate : state = prior.state := by simpa [prior] using hInv.stateEq
  have hsucc := minrunNextN_succ calls (minrunInit listSize)
  have hnextState :
    (minrunNext state).state =
      (minrunNextN (calls + 1) (minrunInit listSize)).state := by
    rwa [hstate]
  have houtputs :
    (minrunNextN (calls + 1) (minrunInit listSize)).outputs =
      (minrunNextN calls (minrunInit listSize)).outputs ++
        [(minrunNext state).result.toNat] := by
    rwa [hstate]
  have hpositive : 0 < listSize.toNat := by omega
  have hbounds := minrunNext_after_init_bounds listSize hInv.listNonnegative
    hInv.listMax hpositive calls
  dsimp only at hbounds
  rw [← hstate] at hbounds
  exact
    { assertionPassed := hbounds.1
      targetPositive := hbounds.2.1
      targetMax := hbounds.2.2
      nextState := hnextState
      emittedOutputs := houtputs }

end CPythonListsort

namespace CPythonListsort

/--
[AdaptiveMinrunScanInvariant.advance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma AdaptiveMinrunScanInvariant.advance
  {κ : Type u}
  {ν : Type v}
  {listSize : PySSize}
  {calls scanned consumed : Nat}
  {state : MinrunState}
-- given
  (hInv : AdaptiveMinrunScanInvariant listSize calls scanned state)
  (hActive : scanned < listSize.toNat)
  (hTargetConsumed : (minrunNext state).result.toNat ≤ consumed)
  (hNextScanned : scanned + consumed ≤ listSize.toNat) :
-- imply
  AdaptiveMinrunScanInvariant listSize (calls + 1) (scanned + consumed) (minrunNext state).state := by
-- proof
  have hstep := adaptiveMinrun_step_facts hInv hActive
  refine
    { listNonnegative := hInv.listNonnegative
      listMax := hInv.listMax
      stateEq := hstep.nextState
      emittedLeScanned := ?_
      scannedBound := hNextScanned }
  rw [hstep.emittedOutputs, List.sum_append]
  simp only [List.sum_singleton]
  exact Nat.add_le_add hInv.emittedLeScanned hTargetConsumed

end CPythonListsort

namespace CPythonListsort

/--
[PendingLayout.pending_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma PendingLayout.pending_nonempty
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned : Nat}
-- given
  (hLayout : PendingLayout state scanned)
  (hScanned : 0 < scanned) :
-- imply
  state.pending.toList ≠ [] := by
-- proof
  intro hempty
  have hcover := hLayout.2.2.2
  rw [hempty] at hcover
  simp [PendingRunsCover] at hcover
  omega

end CPythonListsort

namespace CPythonListsort

/--
[installMinrunState_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma installMinrunState_frame
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {minrun : MinrunState} :
-- imply
  let after := installMinrunState state minrun after.minrunState = minrun ∧ after.min_gallop = state.min_gallop ∧ after.basekeys = state.basekeys ∧ after.data = state.data ∧ after.a = state.a ∧ after.alloced = state.alloced ∧ after.pending = state.pending ∧ after.key_compare = state.key_compare := by
-- proof
  simp [installMinrunState, MergeState.minrunState]

end CPythonListsort

namespace CPythonListsort

/--
[pushPendingRun_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma pushPendingRun_frame
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {run : PendingRun} :
-- imply
  let after := pushPendingRun state run after.listlen = state.listlen ∧ after.basekeys = state.basekeys ∧ after.data = state.data ∧ after.a = state.a ∧ after.alloced = state.alloced ∧ after.key_compare = state.key_compare ∧ after.minrunState = state.minrunState ∧ after.pending.toList = state.pending.toList ++ [run] := by
-- proof
  simp [pushPendingRun, MergeState.minrunState]

end CPythonListsort

namespace CPythonListsort

/--
[pushPendingRun_preserves_activePackage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma pushPendingRun_preserves_activePackage
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {run : PendingRun}
-- given
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
-- imply
  TempStorageInv (pushPendingRun state run).a (pushPendingRun state run).alloced ∧ (pushPendingRun state run).a.Live ∧ SortSlice.ValuesModeInvariant (pushPendingRun state run).a.hasValues (pushPendingRun state run).data ∧ (pushPendingRun state run).a.hasValues = state.a.hasValues := by
-- proof
  constructor
  · simpa [pushPendingRun] using hInv
  constructor
  · simpa [pushPendingRun] using hLive
  constructor
  · simpa [pushPendingRun] using hMode
  · simp [pushPendingRun]

end CPythonListsort

namespace CPythonListsort

/--
[mergeFreemem_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma mergeFreemem_frame
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
-- given
  (hInv : TempStorageInv state.a state.alloced) :
-- imply
  let after := mergeFreemem state after.listlen = state.listlen ∧ after.basekeys = state.basekeys ∧ after.data = state.data ∧ after.alloced = state.alloced ∧ after.pending = state.pending ∧ after.key_compare = state.key_compare ∧ after.minrunState = state.minrunState ∧ after.a.hasValues = state.a.hasValues ∧ TempStorageInv after.a after.alloced := by
-- proof
  unfold mergeFreemem
  split <;> simp_all [MergeState.minrunState, TempStorageInv]

end CPythonListsort

namespace CPythonListsort

/--
[finalReversePhase_sourceValid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma finalReversePhase_sourceValid
  {κ : Type u}
  {ν : Type v}
-- given
  (hasValues : Bool) :
-- imply
  finalReversePhase hasValues = .keys ∨ hasValues = true := by
-- proof
  cases hasValues <;> simp [finalReversePhase]

end CPythonListsort

namespace CPythonListsort

/--
[erase_finalReversePhaseTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma erase_finalReversePhaseTraced
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
-- given
  (hasValues : Bool)
  (lo hi : Int) :
-- imply
  (reverseSlicePhaseTraced? (finalReversePhase hasValues) slice lo hi).erase = reverseSlice? slice lo hi :=
-- proof
erase_reverseSlicePhaseTraced _ _ _ _

end CPythonListsort

namespace CPythonListsort

/--
[finalReversePhase_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
lemma finalReversePhase_safe
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
-- given
  (hasValues : Bool)
  (lo hi : Int)
  (hlo : 0 ≤ lo)
  (hhi : hi ≤ Int.ofNat slice.entries.size)
  (hordered : lo ≤ hi)
  (hMode : SortSlice.ValuesModeInvariant hasValues slice) :
-- imply
  ∃ result, ReverseSlicePhaseSafetyPost (finalReversePhase hasValues) slice lo hi hasValues result := by
-- proof
  exact reverseSlicePhaseTraced_safe (finalReversePhase hasValues) slice lo hi
    hasValues hlo hhi hordered (finalReversePhase_sourceValid hasValues) hMode

end CPythonListsort

/--
[listSizeWord_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean)
-/
@[path]
private lemma listSizeWord_toNat_eq
  {κ : Type u}
  {ν : Type v}
  {size : Nat}
-- given
  (hsize : size ≤ PY_LIST_MAX) :
-- imply
  (BitVec.ofNat 64 size : PySSize).toNat = size := by
-- proof
  apply CPythonListsort.listSizeWord_toNat hsize


-- created on 2026-10-23
