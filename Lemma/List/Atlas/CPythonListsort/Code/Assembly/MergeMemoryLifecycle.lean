import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.MergeMemoryLifecycle
open CPythonListsort CPythonListsort.MergeMemorySnapshot CPythonListsort.MergeMemoryCallEvent CPythonListsort.MergeMemoryEvent CPythonListsort.AccessTrace CPythonListsort.AccessTrace.MergeMemoryCallChain


namespace CPythonListsort.MergeMemorySnapshot

/--
[StorageInv.physicalSlots_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma StorageInv.physicalSlots_eq
  {snapshot : MergeMemorySnapshot}
-- given
  (hInv : snapshot.StorageInv) :
-- imply
  snapshot.physicalSlots = snapshot.multiplier * snapshot.cellsSize :=
-- proof
  hInv.1

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.MergeMemorySnapshot

/--
[storageInv_rejects_phantomPhysicalSlots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma storageInv_rejects_phantomPhysicalSlots
  {snapshot : MergeMemorySnapshot}
-- given
  (hWrong : snapshot.physicalSlots ≠ snapshot.multiplier * snapshot.cellsSize) :
-- imply
  ¬ snapshot.StorageInv := by
-- proof
  intro hInv
  exact hWrong hInv.physicalSlots_eq

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.MergeMemorySnapshot

/--
[allocationLimit_ofState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma allocationLimit_ofState
  {state : MergeState κ ν} :
-- imply
  (ofState state).allocationLimit = mergeGetmemAllocationLimit state.a := by
-- proof
  rfl

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.MergeMemorySnapshot

/--
[storageInv_ofState_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma storageInv_ofState_iff
  {state : MergeState κ ν} :
-- imply
  (ofState state).StorageInv ↔ TempStorageInv state.a state.alloced := by
-- proof
  cases hbacking : state.a.backing <;>
    simp [StorageInv, ofState, TempStorageInv, hbacking,
      multiplier, TempStorage.multiplier, TempStorage.physicalSlots,
      Array.isEmpty_iff]
  all_goals aesop

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.MergeMemorySnapshot

/--
[live_ofState_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma live_ofState_iff
  {state : MergeState κ ν} :
-- imply
  (ofState state).Live ↔ state.a.Live := by
-- proof
  simp [Live, ofState, TempStorage.Live]

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.MergeMemorySnapshot

/--
[physicalBound_ofState_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma physicalBound_ofState_iff
  {state : MergeState κ ν} :
-- imply
  (ofState state).PhysicalBound ↔ state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
-- proof
  rfl

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.MergeMemorySnapshot

/--
[value_isSome_eq_mode_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
private lemma value_isSome_eq_mode_iff
  (mode : Bool) (entry : SortSliceEntry κ ν) :
  entry.value.isSome = mode ↔
    SortSlice.EntryMatchesValuesMode mode entry := by
  cases mode <;> cases hvalue : entry.value <;>
    simp [SortSlice.EntryMatchesValuesMode, hvalue]

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.MergeMemorySnapshot

/--
[valuesMode_ofState_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma valuesMode_ofState_iff
  {mode : Bool}
  {state : MergeState κ ν} :
-- imply
  (ofState state).ValuesMode mode ↔ state.a.hasValues = mode ∧ SortSlice.ValuesModeInvariant mode state.data := by
-- proof
  constructor
  · intro hsnapshot
    refine ⟨hsnapshot.1, ?_⟩
    intro i hi
    have hpresence := hsnapshot.2 i (by
      simpa [ofState] using hi)
    have hpresence' : state.data.entries[i].value.isSome = mode := by
      simpa [ofState, List.getElem_map, Array.getElem_toList] using hpresence
    exact (value_isSome_eq_mode_iff mode state.data.entries[i]).mp hpresence'
  · rintro ⟨hbit, hmode⟩
    refine ⟨hbit, ?_⟩
    intro i hi
    have hiArray : i < state.data.entries.size := by
      simpa [ofState] using hi
    have hpresent :=
      (value_isSome_eq_mode_iff mode state.data.entries[i]).mpr
        (hmode i hiArray)
    simpa [ofState, List.getElem_map, Array.getElem_toList] using hpresent

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.MergeMemorySnapshot

/--
[activeCore_ofState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma activeCore_ofState
  {mode : Bool}
  {state : MergeState κ ν}
-- given
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hBit : state.a.hasValues = mode)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
-- imply
  (ofState state).ActiveCore mode := by
-- proof
  refine ⟨(storageInv_ofState_iff state).2 hInv,
    (live_ofState_iff state).2 hLive, ?_, ?_⟩
  · exact TempStorageInv.cells_size_eq hInv hLive
  · apply (valuesMode_ofState_iff mode state).2
    refine ⟨hBit, ?_⟩
    simpa [hBit] using hMode

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.MergeMemoryCallEvent

/--
[isFreedFrom_ofState_mergeFreemem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma isFreedFrom_ofState_mergeFreemem
  {state : MergeState κ ν} :
-- imply
  IsFreedFrom (MergeMemorySnapshot.ofState state) (MergeMemorySnapshot.ofState (mergeFreemem state)) := by
-- proof
  cases hbacking : state.a.backing <;>
    simp [IsFreedFrom, MergeMemorySnapshot.ofState, mergeFreemem,
      hbacking, TempStorage.physicalSlots]

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[actual_getmemValid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
event contract whenever the exact C allocation guard is discharged. -/
private lemma actual_getmemValid
  (direction : MergeMemoryDirection) (state : MergeState κ ν)
  (need : PySSize) (na nb : Nat) (left right listlen : PySSize)
  (hLimit : need.toNat ≤ mergeGetmemAllocationLimit state.a) :
  let allocated := mergeGetmem state need
  let call : MergeMemoryCallEvent :=
    { direction := direction
      request := need
      na := na
      nb := nb
      sourceLeftLength := left
      sourceRightLength := right
      listlen := listlen
      outcome := allocated.outcome
      before := MergeMemorySnapshot.ofState state
      intermediateFree := mergeMemoryIntermediateFree state need
      afterGetmem := MergeMemorySnapshot.ofState allocated.state
      afterMerge := MergeMemorySnapshot.ofState allocated.state }
  call.GetmemValid := by
  dsimp only
  by_cases hReuse : need.sle state.alloced = true
  · left
    rw [mergeGetmem_reused state need hReuse]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · simpa [MergeMemorySnapshot.ofState] using hReuse
    · simp [mergeMemoryIntermediateFree, hReuse]
  · have hReuseFalse : need.sle state.alloced = false :=
    Bool.eq_false_of_not_eq_true hReuse
    right
    have hGrown := mergeGetmem_grown state need hReuseFalse hLimit
    simp only at hGrown
    rcases hGrown with
      ⟨hOutcome, hAlloced, hBacking, hValues, hCells⟩
    refine ⟨hOutcome, hReuseFalse, ?_⟩
    refine ⟨MergeMemorySnapshot.ofState (mergeFreemem state), ?_,
      isFreedFrom_ofState_mergeFreemem state, hLimit, ?_⟩
    · simp [mergeMemoryIntermediateFree, hReuseFalse]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [MergeMemorySnapshot.ofState] using hBacking
    · simpa [MergeMemorySnapshot.ofState] using hValues
    · simpa [MergeMemorySnapshot.ofState] using hAlloced
    · simpa [MergeMemorySnapshot.ofState] using
      congrArg Array.size hCells
    · have hPhysical :=
      mergeGetmem_grown_physicalSlots state need hReuseFalse hLimit
      by_cases hValuesBit : state.a.hasValues = true
      · simpa [MergeMemorySnapshot.ofState, MergeMemorySnapshot.multiplier,
        TempStorage.multiplier, hValuesBit] using hPhysical
      · simpa [MergeMemorySnapshot.ofState, MergeMemorySnapshot.multiplier,
        TempStorage.multiplier, hValuesBit] using hPhysical
    · have hData := mergeGetmem_nonStorageFrame state need
      exact congrArg
        (fun frame =>
          frame.data.entries.toList.map fun entry => entry.value.isSome)
        hData

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeLoMemoryCallEvent_getmemValid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeLoMemoryCallEvent_getmemValid
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
  {execution : TraceResult (MergeLoResult κ ν)}
  {result : MergeLoResult κ ν}
  {post : MergeLoSafetyPost pre scanned i call execution result} :
-- imply
  (mergeLoMemoryCallEvent call result).GetmemValid := by
-- proof
  simpa only [mergeLoMemoryCallEvent, mergeLoAllocated, GetmemValid] using
    actual_getmemValid (.lo) call.state (BitVec.ofNat 64 call.na)
      call.na call.nb call.left.len call.right.len call.state.listlen
      post.requestFacts.requestWithinLimit

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeHiMemoryCallEvent_getmemValid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeHiMemoryCallEvent_getmemValid
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
  {execution : TraceResult (MergeHiResult κ ν)}
  {result : MergeHiResult κ ν}
  {post : MergeHiSafetyPost pre scanned i call execution result} :
-- imply
  (mergeHiMemoryCallEvent call result).GetmemValid := by
-- proof
  simpa only [mergeHiMemoryCallEvent, mergeHiAllocated, GetmemValid] using
    actual_getmemValid (.hi) call.state (BitVec.ofNat 64 call.nb)
      call.na call.nb call.left.len call.right.len call.state.listlen
      post.requestFacts.requestWithinLimit

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[activeCore_of_getmemStoragePost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma activeCore_of_getmemStoragePost
  {mode : Bool}
  {before : MergeState κ ν}
  {need : PySSize}
  {result : MergeGetmemResult κ ν}
  {post : MergeGetmemStoragePost before need result}
-- given
  (hBit : before.a.hasValues = mode)
  (hMode : SortSlice.ValuesModeInvariant before.a.hasValues before.data) :
-- imply
  (MergeMemorySnapshot.ofState result.state).ActiveCore mode := by
-- proof
  apply MergeMemorySnapshot.activeCore_ofState mode result.state
    post.invariant post.live (post.valuesMode.trans hBit)
  rwa [post.data_eq, post.valuesMode]

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[keySlots_of_getmemStoragePost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma keySlots_of_getmemStoragePost
  {before : MergeState κ ν}
  {need : PySSize}
  {result : MergeGetmemResult κ ν}
  {post : MergeGetmemStoragePost before need result} :
-- imply
  ∀ i, i < need.toNat → i < result.state.a.physicalSlots := by
-- proof
  intro i hi
  have hfit := post.requestFits
  have hslots := post.physicalSlots
  cases hValues : result.state.a.hasValues <;>
    simp [TempStorage.multiplier, hValues] at hslots <;> omega

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[valueSlots_of_getmemStoragePost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma valueSlots_of_getmemStoragePost
  {before : MergeState κ ν}
  {need : PySSize}
  {result : MergeGetmemResult κ ν}
  {post : MergeGetmemStoragePost before need result}
-- given
  (hValues : before.a.hasValues = true) :
-- imply
  ∀ i, i < need.toNat → result.state.alloced.toNat + i < result.state.a.physicalSlots := by
-- proof
  intro i hi
  have hfit := post.requestFits
  have hResultValues : result.state.a.hasValues = true :=
    post.valuesMode.trans hValues
  have hslots := post.physicalSlots
  simp [TempStorage.multiplier, hResultValues] at hslots
  omega

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[physicalBound_of_getmemStoragePost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma physicalBound_of_getmemStoragePost
  {before : MergeState κ ν}
  {need : PySSize}
  {result : MergeGetmemResult κ ν}
  {post : MergeGetmemStoragePost before need result}
-- given
  (hBefore : before.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
-- imply
  result.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
-- proof
  obtain hReuse | hGrowth := post.outcome
  · rw [post.reuseAccounting hReuse]
    exact hBefore
  · exact (post.growthAccounting hGrowth).2.2.2.2

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[physicalBound_of_mergeFreemem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma physicalBound_of_mergeFreemem
  {state : MergeState κ ν}
-- given
  (hBefore : (MergeMemorySnapshot.ofState state).PhysicalBound) :
-- imply
  (MergeMemorySnapshot.ofState (mergeFreemem state)).PhysicalBound := by
-- proof
  cases hBacking : state.a.backing
  · simpa [MergeMemorySnapshot.PhysicalBound,
    MergeMemorySnapshot.ofState, mergeFreemem, hBacking,
    TempStorage.physicalSlots] using hBefore
  · simp [MergeMemorySnapshot.PhysicalBound,
    MergeMemorySnapshot.ofState, mergeFreemem, hBacking,
    TempStorage.physicalSlots]
  · simp [MergeMemorySnapshot.PhysicalBound,
    MergeMemorySnapshot.ofState, mergeFreemem, hBacking,
    TempStorage.physicalSlots]

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[valid_rejects_guardRejected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma valid_rejects_guardRejected
  {mode : Bool}
  {call : MergeMemoryCallEvent}
-- given
  (hRejected : call.outcome = .guardRejected) :
-- imply
  ¬ call.Valid mode := by
-- proof
  intro hValid
  exact hValid.neverGuardRejected hRejected

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeLoMemoryCallEvent_mergeStorageFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeLoMemoryCallEvent_mergeStorageFrame
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
  {execution : TraceResult (MergeLoResult κ ν)}
  {result : MergeLoResult κ ν}
  {post : MergeLoSafetyPost pre scanned i call execution result} :
-- imply
  (mergeLoMemoryCallEvent call result).MergeStorageFrame := by
-- proof
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.backing
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.hasValues
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.cellsSize
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.alloced
  · simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.physicalSlots_eq
  · simp only [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState,
    List.length_map, Array.length_toList]
    rw [post.stableFrame.dataSize, post.allocationPost.data_eq]

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeHiMemoryCallEvent_mergeStorageFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeHiMemoryCallEvent_mergeStorageFrame
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
  {execution : TraceResult (MergeHiResult κ ν)}
  {result : MergeHiResult κ ν}
  {post : MergeHiSafetyPost pre scanned i call execution result} :
-- imply
  (mergeHiMemoryCallEvent call result).MergeStorageFrame := by
-- proof
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.backing
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.hasValues
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.cellsSize
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.alloced
  · simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.postGetmemStorageFrame.physicalSlots_eq
  · simp only [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState,
    List.length_map, Array.length_toList]
    rw [post.stableFrame.dataSize, post.allocationPost.data_eq]

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeLoMemoryCallEvent_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeLoMemoryCallEvent_valid
  {mode : Bool}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
  {execution : TraceResult (MergeLoResult κ ν)}
  {result : MergeLoResult κ ν}
  {post : MergeLoSafetyPost pre scanned i call execution result}
-- given
  (hBit : call.state.a.hasValues = mode) :
-- imply
  (mergeLoMemoryCallEvent call result).Valid mode := by
-- proof
  have hDispatch : call.na ≤ call.nb := by
    obtain hLo | hHi := post.requestFacts.sourceDispatch
    · exact hLo.2
    · omega
  have hFinalBit : result.state.a.hasValues = mode :=
    post.stableFrame.tempValuesMode.trans hBit
  refine
    { beforeActive := MergeMemorySnapshot.activeCore_ofState mode call.state
      post.inputTempInvariant post.inputTempLive hBit post.inputValuesMode
      getmemActive := activeCore_of_getmemStoragePost mode call.state
        (BitVec.ofNat 64 call.na) (mergeLoAllocated call)
        post.allocationPost hBit post.inputValuesMode
      afterMergeActive := MergeMemorySnapshot.activeCore_ofState mode
        result.state post.tempInvariant post.tempLive hFinalBit post.valuesMode
      requestWord := ?_
      requestNonnegative := ?_
      directionalRequest := ?_
      trimmingOnlyShrinks := post.requestFacts.runLengthChain.1
      sourceRunsWithinList := ?_
      smallerHalf := ?_
      keyedLimit := ?_
      unkeyedLimit := ?_
      requestWithinLimit := ?_
      getmem := ?_
      neverGuardRejected := ?_
      requestFits := ?_
      keySlots := ?_
      valueSlots := ?_
      mergeStorageFrame := mergeLoMemoryCallEvent_mergeStorageFrame
        pre scanned i call execution result post
      physicalBoundPreserved := ?_ }
  · simpa [mergeLoMemoryCallEvent] using congrArg (BitVec.ofNat 64)
    post.requestFacts.requestIsMinimum
  · simpa [mergeLoMemoryCallEvent] using
    post.requestFacts.requestNonnegative
  · left
    exact ⟨rfl, by simpa [mergeLoMemoryCallEvent] using
      post.requestFacts.requestRoundtrip, hDispatch⟩
  · simp only [mergeLoMemoryCallEvent]
    rwa [post.requestFacts.listlenFrame]
      post.requestFacts.runLengthChain.2.2
  · simp only [mergeLoMemoryCallEvent]
    rwa [post.requestFacts.listlenFrame]
  · intro hValues
    simpa only [mergeLoMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.keyedLimit hValues
  · intro hValues
    simpa only [mergeLoMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.unkeyedLimit hValues
  · simpa only [mergeLoMemoryCallEvent,
    MergeMemorySnapshot.allocationLimit_ofState] using
    post.requestFacts.requestWithinLimit
  · exact mergeLoMemoryCallEvent_getmemValid
    pre scanned i call execution result post
  · simpa only [mergeLoMemoryCallEvent, mergeLoAllocated] using
    post.requestFacts.guardNotRejected
  · simpa only [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.allocationPost.requestFits
  · simpa only [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
    keySlots_of_getmemStoragePost call.state (BitVec.ofNat 64 call.na)
      (mergeLoAllocated call) post.allocationPost
  · intro hValues
    simpa only [mergeLoMemoryCallEvent, MergeMemorySnapshot.ofState] using
      valueSlots_of_getmemStoragePost call.state (BitVec.ofNat 64 call.na)
        (mergeLoAllocated call) post.allocationPost hValues
  · intro hBefore
    have hBefore' : call.state.a.physicalSlots ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
      simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.PhysicalBound,
        MergeMemorySnapshot.ofState] using hBefore
    have hAllocated := physicalBound_of_getmemStoragePost call.state
      (BitVec.ofNat 64 call.na) (mergeLoAllocated call)
      post.allocationPost hBefore'
    exact ⟨by simpa [mergeLoMemoryCallEvent,
      MergeMemorySnapshot.PhysicalBound, MergeMemorySnapshot.ofState] using
        hAllocated,
      by simpa [mergeLoMemoryCallEvent, MergeMemorySnapshot.PhysicalBound,
        MergeMemorySnapshot.ofState] using post.physicalSlotsBound hBefore'⟩

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeHiMemoryCallEvent_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeHiMemoryCallEvent_valid
  {mode : Bool}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
  {execution : TraceResult (MergeHiResult κ ν)}
  {result : MergeHiResult κ ν}
  {post : MergeHiSafetyPost pre scanned i call execution result}
-- given
  (hBit : call.state.a.hasValues = mode) :
-- imply
  (mergeHiMemoryCallEvent call result).Valid mode := by
-- proof
  have hFinalBit : result.state.a.hasValues = mode :=
    post.stableFrame.tempValuesMode.trans hBit
  refine
    { beforeActive := MergeMemorySnapshot.activeCore_ofState mode call.state
      post.inputTempInvariant post.inputTempLive hBit post.inputValuesMode
      getmemActive := activeCore_of_getmemStoragePost mode call.state
        (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
        post.allocationPost hBit post.inputValuesMode
      afterMergeActive := MergeMemorySnapshot.activeCore_ofState mode
        result.state post.tempInvariant post.tempLive hFinalBit post.valuesMode
      requestWord := ?_
      requestNonnegative := ?_
      directionalRequest := ?_
      trimmingOnlyShrinks := post.requestFacts.runLengthChain.1
      sourceRunsWithinList := ?_
      smallerHalf := ?_
      keyedLimit := ?_
      unkeyedLimit := ?_
      requestWithinLimit := ?_
      getmem := ?_
      neverGuardRejected := ?_
      requestFits := ?_
      keySlots := ?_
      valueSlots := ?_
      mergeStorageFrame := mergeHiMemoryCallEvent_mergeStorageFrame
        pre scanned i call execution result post
      physicalBoundPreserved := ?_ }
  · simpa [mergeHiMemoryCallEvent] using congrArg (BitVec.ofNat 64)
    post.requestFacts.requestIsMinimum
  · simpa [mergeHiMemoryCallEvent] using
    post.requestFacts.requestNonnegative
  · right
    exact ⟨rfl, by simpa [mergeHiMemoryCallEvent] using
      post.requestFacts.requestRoundtrip, post.directionalDispatch⟩
  · simp only [mergeHiMemoryCallEvent]
    rwa [post.requestFacts.listlenFrame]
      post.requestFacts.runLengthChain.2.2
  · simp only [mergeHiMemoryCallEvent]
    rwa [post.requestFacts.listlenFrame]
  · intro hValues
    simpa only [mergeHiMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.keyedLimit hValues
  · intro hValues
    simpa only [mergeHiMemoryCallEvent,
      MergeMemorySnapshot.allocationLimit_ofState] using
      post.requestFacts.unkeyedLimit hValues
  · simpa only [mergeHiMemoryCallEvent,
    MergeMemorySnapshot.allocationLimit_ofState] using
    post.requestFacts.requestWithinLimit
  · exact mergeHiMemoryCallEvent_getmemValid
    pre scanned i call execution result post
  · simpa only [mergeHiMemoryCallEvent, mergeHiAllocated] using
    post.requestFacts.guardNotRejected
  · simpa only [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
    post.allocationPost.requestFits
  · simpa only [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
    keySlots_of_getmemStoragePost call.state (BitVec.ofNat 64 call.nb)
      (mergeHiAllocated call) post.allocationPost
  · intro hValues
    simpa only [mergeHiMemoryCallEvent, MergeMemorySnapshot.ofState] using
      valueSlots_of_getmemStoragePost call.state (BitVec.ofNat 64 call.nb)
        (mergeHiAllocated call) post.allocationPost hValues
  · intro hBefore
    have hBefore' : call.state.a.physicalSlots ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
      simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.PhysicalBound,
        MergeMemorySnapshot.ofState] using hBefore
    have hAllocated := physicalBound_of_getmemStoragePost call.state
      (BitVec.ofNat 64 call.nb) (mergeHiAllocated call)
      post.allocationPost hBefore'
    exact ⟨by simpa [mergeHiMemoryCallEvent,
      MergeMemorySnapshot.PhysicalBound, MergeMemorySnapshot.ofState] using
        hAllocated,
      by simpa [mergeHiMemoryCallEvent, MergeMemorySnapshot.PhysicalBound,
        MergeMemorySnapshot.ofState] using post.physicalSlotsBound hBefore'⟩

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeLoMemoryCallEvent_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeLoMemoryCallEvent_bounded
  {mode : Bool}
  {call : MergeAtCall κ ν}
  {result : MergeLoResult κ ν}
-- given
  (hValid : (mergeLoMemoryCallEvent call result).Valid mode)
  (hBefore : call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
-- imply
  (mergeLoMemoryCallEvent call result).Bounded := by
-- proof
  have hBeforeSnapshot :
    (MergeMemorySnapshot.ofState call.state).PhysicalBound := by
    simpa [MergeMemorySnapshot.PhysicalBound,
      MergeMemorySnapshot.ofState] using hBefore
  have hAfter := hValid.physicalBoundPreserved (by
    simpa [mergeLoMemoryCallEvent] using hBeforeSnapshot)
  refine ⟨by simpa [mergeLoMemoryCallEvent] using hBeforeSnapshot,
    hAfter.1, hAfter.2, ?_⟩
  intro freed hFreed
  by_cases hReuse :
    (BitVec.ofNat 64 call.na).sle call.state.alloced = true
  · simp [mergeLoMemoryCallEvent, mergeMemoryIntermediateFree,
    hReuse] at hFreed
  · have hReuseFalse :
    (BitVec.ofNat 64 call.na).sle call.state.alloced = false :=
    Bool.eq_false_of_not_eq_true hReuse
    have hFreedEq :
      freed = MergeMemorySnapshot.ofState (mergeFreemem call.state) := by
      symm
      simpa [mergeLoMemoryCallEvent, mergeMemoryIntermediateFree,
        hReuseFalse] using hFreed
    rw [hFreedEq]
    exact physicalBound_of_mergeFreemem call.state hBeforeSnapshot

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeHiMemoryCallEvent_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeHiMemoryCallEvent_bounded
  {mode : Bool}
  {call : MergeAtCall κ ν}
  {result : MergeHiResult κ ν}
-- given
  (hValid : (mergeHiMemoryCallEvent call result).Valid mode)
  (hBefore : call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
-- imply
  (mergeHiMemoryCallEvent call result).Bounded := by
-- proof
  have hBeforeSnapshot :
    (MergeMemorySnapshot.ofState call.state).PhysicalBound := by
    simpa [MergeMemorySnapshot.PhysicalBound,
      MergeMemorySnapshot.ofState] using hBefore
  have hAfter := hValid.physicalBoundPreserved (by
    simpa [mergeHiMemoryCallEvent] using hBeforeSnapshot)
  refine ⟨by simpa [mergeHiMemoryCallEvent] using hBeforeSnapshot,
    hAfter.1, hAfter.2, ?_⟩
  intro freed hFreed
  by_cases hReuse :
    (BitVec.ofNat 64 call.nb).sle call.state.alloced = true
  · simp [mergeHiMemoryCallEvent, mergeMemoryIntermediateFree,
    hReuse] at hFreed
  · have hReuseFalse :
    (BitVec.ofNat 64 call.nb).sle call.state.alloced = false :=
    Bool.eq_false_of_not_eq_true hReuse
    have hFreedEq :
      freed = MergeMemorySnapshot.ofState (mergeFreemem call.state) := by
      symm
      simpa [mergeHiMemoryCallEvent, mergeMemoryIntermediateFree,
        hReuseFalse] using hFreed
    rw [hFreedEq]
    exact physicalBound_of_mergeFreemem call.state hBeforeSnapshot

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeLoMemoryCallEvent_bounded_of_post](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeLoMemoryCallEvent_bounded_of_post
  {mode : Bool}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
  {execution : TraceResult (MergeLoResult κ ν)}
  {result : MergeLoResult κ ν}
  {post : MergeLoSafetyPost pre scanned i call execution result}
-- given
  (hBit : call.state.a.hasValues = mode)
  (hBefore : call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
-- imply
  (mergeLoMemoryCallEvent call result).Bounded :=
-- proof
  mergeLoMemoryCallEvent_bounded mode call result
    (mergeLoMemoryCallEvent_valid mode pre scanned i call execution result
      post hBit)
    hBefore

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryCallEvent

/--
[mergeHiMemoryCallEvent_bounded_of_post](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeHiMemoryCallEvent_bounded_of_post
  {mode : Bool}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
  {execution : TraceResult (MergeHiResult κ ν)}
  {result : MergeHiResult κ ν}
  {post : MergeHiSafetyPost pre scanned i call execution result}
-- given
  (hBit : call.state.a.hasValues = mode)
  (hBefore : call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES) :
-- imply
  (mergeHiMemoryCallEvent call result).Bounded :=
-- proof
  mergeHiMemoryCallEvent_bounded mode call result
    (mergeHiMemoryCallEvent_valid mode pre scanned i call execution result
      post hBit)
    hBefore

end CPythonListsort.MergeMemoryCallEvent

namespace CPythonListsort.MergeMemoryEvent

/--
[cleanupValid_ofState_mergeFreemem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma cleanupValid_ofState_mergeFreemem
  {mode : Bool}
  {state : MergeState κ ν}
-- given
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hBit : state.a.hasValues = mode)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
-- imply
  CleanupValid mode (MergeMemorySnapshot.ofState state) (MergeMemorySnapshot.ofState (mergeFreemem state)) := by
-- proof
  refine ⟨MergeMemorySnapshot.activeCore_ofState mode state hInv hLive hBit
    hMode, ?_, ?_, MergeMemoryCallEvent.isFreedFrom_ofState_mergeFreemem state⟩
  · exact (MergeMemorySnapshot.storageInv_ofState_iff
    (mergeFreemem state)).2 (mergeFreemem_tempStorageInv state hInv)
  · apply (MergeMemorySnapshot.valuesMode_ofState_iff mode
    (mergeFreemem state)).2
    refine ⟨?_, ?_⟩
    · by_cases hInline : state.a.backing = .inline <;>
      simp [mergeFreemem, hInline, hBit]
    · by_cases hInline : state.a.backing = .inline <;>
      simpa [mergeFreemem, hInline, hBit] using hMode

end CPythonListsort.MergeMemoryEvent

namespace CPythonListsort.AccessTrace.MergeMemoryCallChain

/--
[nil_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma nil_iff
  {start final : MergeMemorySnapshot} :
-- imply
  MergeMemoryCallChain start [] final ↔ start = final := by
-- proof
  rfl

end CPythonListsort.AccessTrace.MergeMemoryCallChain

namespace CPythonListsort.AccessTrace.MergeMemoryCallChain

/--
[cons_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma cons_iff
  {start final : MergeMemorySnapshot}
  {call : MergeMemoryCallEvent}
  {calls : List MergeMemoryCallEvent} :
-- imply
  MergeMemoryCallChain start (call :: calls) final ↔ call.before = start ∧ MergeMemoryCallChain call.afterMerge calls final := by
-- proof
  rfl

end CPythonListsort.AccessTrace.MergeMemoryCallChain

namespace CPythonListsort.AccessTrace.MergeMemoryCallChain

/--
[append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma append
  {start middle final : MergeMemorySnapshot}
  {earlier later : List MergeMemoryCallEvent}
-- given
  (hEarlier : MergeMemoryCallChain start earlier middle)
  (hLater : MergeMemoryCallChain middle later final) :
-- imply
  MergeMemoryCallChain start (earlier ++ later) final := by
-- proof
  induction earlier generalizing start with
  | nil =>
    simpa using hEarlier ▸ hLater
  | cons call calls ih =>
    obtain ⟨hStart, hTail⟩ := hEarlier
    exact ⟨hStart, ih hTail⟩

end CPythonListsort.AccessTrace.MergeMemoryCallChain

namespace CPythonListsort.AccessTrace.MergeMemoryCallChain

/--
[rejects_two_call_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma rejects_two_call_gap
  {start final : MergeMemorySnapshot}
  {first second : MergeMemoryCallEvent}
-- given
  (hGap : second.before ≠ first.afterMerge) :
-- imply
  ¬ MergeMemoryCallChain start [first, second] final := by
-- proof
  intro hChain
  exact hGap hChain.2.1

end CPythonListsort.AccessTrace.MergeMemoryCallChain

namespace CPythonListsort.AccessTrace

/--
[memoryEvents_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma memoryEvents_compose
  {earlier later : AccessTrace} :
-- imply
  (earlier.compose later).memoryEvents = earlier.memoryEvents ++ later.memoryEvents := by
-- proof
  rfl

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[memoryEventsValid_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma memoryEventsValid_empty
  {mode : Bool} :
-- imply
  empty.memoryEventsValid mode := by
-- proof
  simp [memoryEventsValid, empty]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[memoryEventsValid_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma memoryEventsValid_compose
  {mode : Bool}
  {earlier later : AccessTrace} :
-- imply
  (earlier.compose later).memoryEventsValid mode ↔ earlier.memoryEventsValid mode ∧ later.memoryEventsValid mode := by
-- proof
  simp only [memoryEventsValid, memoryEvents_compose, List.mem_append]
  aesop

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[onlyMergeMemoryEvents_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma onlyMergeMemoryEvents_empty
-- imply
  empty.onlyMergeMemoryEvents := by
-- proof
  simp [onlyMergeMemoryEvents, empty]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[onlyMergeMemoryEvents_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma onlyMergeMemoryEvents_compose
  {earlier later : AccessTrace} :
-- imply
  (earlier.compose later).onlyMergeMemoryEvents ↔ earlier.onlyMergeMemoryEvents ∧ later.onlyMergeMemoryEvents := by
-- proof
  simp only [onlyMergeMemoryEvents, memoryEvents_compose, List.mem_append]
  aesop

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[mergeMemoryEventsBounded_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeMemoryEventsBounded_empty
-- imply
  empty.mergeMemoryEventsBounded := by
-- proof
  simp [mergeMemoryEventsBounded, empty]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[mergeMemoryEventsBounded_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeMemoryEventsBounded_compose
  {earlier later : AccessTrace} :
-- imply
  (earlier.compose later).mergeMemoryEventsBounded ↔ earlier.mergeMemoryEventsBounded ∧ later.mergeMemoryEventsBounded := by
-- proof
  simp only [mergeMemoryEventsBounded, memoryEvents_compose, List.mem_append]
  aesop

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[mergeMemorySegment_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeMemorySegment_compose
  {earlier later : AccessTrace}
  {start middle final : MergeMemorySnapshot}
-- given
  (hearlier : earlier.MergeMemorySegment start middle)
  (hlater : later.MergeMemorySegment middle final) :
-- imply
  (earlier.compose later).MergeMemorySegment start final := by
-- proof
  obtain ⟨earlierCalls, hearlierEvents, hearlierChain⟩ := hearlier
  obtain ⟨laterCalls, hlaterEvents, hlaterChain⟩ := hlater
  refine ⟨earlierCalls ++ laterCalls, ?_,
    MergeMemoryCallChain.append hearlierChain hlaterChain⟩
  simp [AccessTrace.compose, hearlierEvents, hlaterEvents, List.map_append]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[mergeMemoryTail_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeMemoryTail_compose
  {earlier later : AccessTrace}
  {start middle final : MergeMemorySnapshot}
-- given
  (hearlier : earlier.MergeMemorySegment start middle)
  (hlater : later.MergeMemoryTail middle final) :
-- imply
  (earlier.compose later).MergeMemoryTail start final := by
-- proof
  obtain ⟨earlierCalls, hearlierEvents, hearlierChain⟩ := hearlier
  rcases hlater with
    ⟨laterCalls, cleanupBefore, hlaterEvents, hlaterChain⟩
  refine ⟨earlierCalls ++ laterCalls, cleanupBefore, ?_,
    MergeMemoryCallChain.append hearlierChain hlaterChain⟩
  simp [AccessTrace.compose, hearlierEvents, hlaterEvents, List.map_append,
    List.append_assoc]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[mergeMemoryLifecycle_prepend_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean)
-/
@[path]
lemma mergeMemoryLifecycle_prepend_initial
  {mode : Bool}
  {initial final : MergeMemorySnapshot}
  {trace : AccessTrace}
-- given
  (hTail : trace.MergeMemoryTail initial final)
  (hInitial : initial.ActiveCore mode)
  (hValid : trace.memoryEventsValid mode)
  (hBounded : trace.mergeMemoryEventsBounded) :
-- imply
  MergeMemoryLifecycle mode initial final ((singletonMemoryEvent (.initial initial)).compose trace) := by
-- proof
  obtain ⟨calls, cleanupBefore, hEvents, hChain⟩ := hTail
  refine ⟨calls, cleanupBefore, ?_, hChain, hInitial, ?_, ?_, ?_⟩
  · simp [AccessTrace.compose, singletonMemoryEvent, hEvents]
  · intro call hCall
    apply hValid (.mergeCall call)
    rw [hEvents]
    simp [hCall]
  · intro call hCall
    have hEvent := hBounded (.mergeCall call) (by
      rw [hEvents]
      simp [hCall])
    exact hEvent
  · apply hValid (.cleanup cleanupBefore final)
    rw [hEvents]
    simp

end CPythonListsort.AccessTrace


-- created on 2026-10-23
