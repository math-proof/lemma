import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Assembly.MergeForceCollapseSafety.Part2
open CPythonListsort CPythonListsort.MergeForceCollapseStableFrame


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[bind_result_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
private lemma TraceResult.bind_result_of_eq_some
  (current : TraceResult α) (next : α → TraceResult β) (value : α)
  (hresult : current.result = some value) :
  (current.bind next).result = (next value).result := by
  change (current.bind next).erase = (next value).erase
  rw [TraceResult.erase_bind]
  change current.result.bind (fun item => (next item).result) = _
  rw [hresult]
  rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[pendingRunRead_result_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
private lemma pendingRunRead_result_of_bounds (state : MergeState κ ν)
  (index : Nat) (hindex : index < state.pending.size) :
  (TraceResult.pendingRunRead? state (Int.ofNat index)).result =
    some state.pending[index] := by
  change (TraceResult.pendingRunRead? state (Int.ofNat index)).erase = _
  rw [TraceResult.erase_pendingRunRead]
  have hnonnegative : 0 ≤ Int.ofNat index := Int.natCast_nonneg _
  rw [if_pos hnonnegative]
  have htoi : (Int.ofNat index).toNat = index := rfl
  rw [htoi]
  exact Array.getElem?_eq_getElem hindex

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[pendingRunRead_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
private lemma pendingRunRead_safe (state : MergeState κ ν) (index : Nat)
  (hindex : index < state.pending.size) :
  MovementTraceSafe
    (TraceResult.pendingRunRead? state (Int.ofNat index)) := by
  constructor
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_pendingRunRead]
    simp only [AccessTrace.allAccessesInBounds,
      AccessTrace.singletonAccess, List.mem_singleton,
      forall_eq, AccessEvent.InBounds]
    exact ⟨Int.natCast_nonneg _, (Int.ofNat_lt).mpr hindex⟩
  · simp [TraceResult.trace_pendingRunRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

/--
[erase_forceCollapseIndexTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma erase_forceCollapseIndexTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  (forceCollapseIndexTraced? state).erase = forceCollapseIndex? state := by
-- proof
  unfold forceCollapseIndexTraced? forceCollapseIndex?
  by_cases hmany : 1 < state.pending.size
  · simp only [hmany, if_true]
    let i := state.pending.size - 2
    by_cases hpositive : 0 < i
    · have hlower : i - 1 < state.pending.size := by omega
      have hupper : i + 1 < state.pending.size := by
        dsimp [i]
        omega
      let previous := state.pending[i - 1]
      let following := state.pending[i + 1]
      have hprevious : state.pending[i - 1]? = some previous :=
        Array.getElem?_eq_getElem hlower
      have hfollowing : state.pending[i + 1]? = some following :=
        Array.getElem?_eq_getElem hupper
      have hpositive' : 0 < state.pending.size - 2 := by
        simpa [i] using hpositive
      rw [if_pos hpositive']
      simp only [TraceResult.erase_bind, TraceResult.erase_pendingRunRead]
      have hlowerNonnegative : 0 ≤ Int.ofNat (i - 1) := Int.natCast_nonneg _
      rw [if_pos hlowerNonnegative]
      have hlowerToNat : (Int.ofNat (i - 1)).toNat = i - 1 := rfl
      rw [hlowerToNat, hprevious]
      rw [if_pos hpositive']
      simp only [Option.bind_some, TraceResult.erase_map,
        TraceResult.erase_pendingRunRead]
      have hupperNonnegative :
        0 ≤ Int.ofNat (state.pending.size - 2 + 1) := Int.natCast_nonneg _
      rw [if_pos hupperNonnegative]
      have hupperToNat :
        (Int.ofNat (state.pending.size - 2 + 1)).toNat =
          state.pending.size - 2 + 1 := rfl
      rw [hupperToNat]
      have hfollowing' :
        state.pending[state.pending.size - 2 + 1]? = some following := by
        simpa [i] using hfollowing
      rw [hfollowing']
      simp only [Option.map_some]
      by_cases hcomparison : previous.len.slt following.len <;>
        simp [hcomparison]
    · have hnotThree : ¬2 < state.pending.size := by
      dsimp [i] at hpositive
      omega
      simp [hnotThree]
  · simp [hmany, TraceResult.erase_failure]

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma forceCollapseIndexTraced_memoryEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  (forceCollapseIndexTraced? state).trace.memoryEvents = [] := by
-- proof
  unfold forceCollapseIndexTraced?
  by_cases hmany : 1 < state.pending.size
  · rw [if_pos hmany]
    dsimp only
    by_cases hpositive : 0 < state.pending.size - 2
    · rw [if_pos hpositive]
      apply TraceResult.memoryEvents_bind_eq_nil
      · simp [TraceResult.trace_pendingRunRead,
        AccessTrace.singletonAccess]
      · intro previous
        simp [TraceResult.memoryEvents_map,
          TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
    · rw [if_neg hpositive]
      rfl
  · rw [if_neg hmany]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_memorySegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma forceCollapseIndexTraced_memorySegment
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  (forceCollapseIndexTraced? state).trace.MergeMemorySegment (MergeMemorySnapshot.ofState state) (MergeMemorySnapshot.ofState state) := by
-- proof
  refine ⟨[], ?_, ?_⟩
  · simpa using forceCollapseIndexTraced_memoryEvents_eq_nil state
  · rfl

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma forceCollapseIndexTraced_safe
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
-- given
  (hmany : 1 < state.pending.size) :
-- imply
  ∃ i, (forceCollapseIndexTraced? state).result = some i ∧ MovementTraceSafe (forceCollapseIndexTraced? state) ∧ (forceCollapseIndexTraced? state).erase = forceCollapseIndex? state ∧ (i + 2 = state.pending.size ∨ i + 3 = state.pending.size) := by
-- proof
  let topPair := state.pending.size - 2
  by_cases hpositive : 0 < topPair
  · have hlower : topPair - 1 < state.pending.size := by omega
    have hupper : topPair + 1 < state.pending.size := by
      dsimp [topPair]
      omega
    let previous := state.pending[topPair - 1]
    let following := state.pending[topPair + 1]
    have hprevious :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (topPair - 1))).result = some previous :=
      pendingRunRead_result_of_bounds state _ hlower
    have hfollowing :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (topPair + 1))).result = some following :=
      pendingRunRead_result_of_bounds state _ hupper
    have hpreviousSafe := pendingRunRead_safe state (topPair - 1) hlower
    have hfollowingSafe := pendingRunRead_safe state (topPair + 1) hupper
    have hselectorSafe : MovementTraceSafe
      ((TraceResult.pendingRunRead? state
        (Int.ofNat (topPair - 1))).bind fun previous =>
          (TraceResult.pendingRunRead? state
            (Int.ofNat (topPair + 1))).map fun following =>
              if previous.len.slt following.len then topPair - 1
              else topPair) := by
      apply MovementTraceSafe.bind _ _ previous hprevious hpreviousSafe
      exact MovementTraceSafe.map _ _ hfollowingSafe
    by_cases hlowerChosen : previous.len.slt following.len
    · refine ⟨topPair - 1, ?_, ?_, erase_forceCollapseIndexTraced state, ?_⟩
      · unfold forceCollapseIndexTraced?
        simp only [hmany, hpositive, if_true, topPair]
        rw [TraceResult.bind_result_of_eq_some _ _ previous hprevious]
        change Option.map _ _ = _
        rw [hfollowing]
        simp [hlowerChosen]
      · simpa [forceCollapseIndexTraced?, hmany, hpositive, topPair] using
        hselectorSafe
      · right
        dsimp [topPair]
        omega
    · refine ⟨topPair, ?_, ?_, erase_forceCollapseIndexTraced state, ?_⟩
      · unfold forceCollapseIndexTraced?
        simp only [hmany, hpositive, if_true, topPair]
        rw [TraceResult.bind_result_of_eq_some _ _ previous hprevious]
        change Option.map _ _ = _
        rw [hfollowing]
        simp [hlowerChosen]
      · simpa [forceCollapseIndexTraced?, hmany, hpositive, topPair] using
        hselectorSafe
      · left
        dsimp [topPair]
        omega
  · have htopPair : topPair = 0 := by omega
    have hsize : state.pending.size = 2 := by
      dsimp [topPair] at hpositive
      omega
    refine ⟨0, ?_, ?_, erase_forceCollapseIndexTraced state, ?_⟩
    · simp [forceCollapseIndexTraced?, hsize]
      rfl
    · simpa [forceCollapseIndexTraced?, hsize] using
      (MovementTraceSafe.pure (0 : Nat))
    · left
      dsimp [topPair] at htopPair
      omega

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_neighbor_access_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma forceCollapseIndexTraced_neighbor_access_order
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
-- given
  (hthree : 2 < state.pending.size) :
-- imply
  (forceCollapseIndexTraced? state).trace.accesses = [{ kind := .read, region := .pendingRuns, index := Int.ofNat (state.pending.size - 3), extent := state.pending.size }, { kind := .read, region := .pendingRuns, index := Int.ofNat (state.pending.size - 1), extent := state.pending.size }] := by
-- proof
  have hmany : 1 < state.pending.size := by omega
  have hlower : state.pending.size - 3 < state.pending.size := by omega
  let previous := state.pending[state.pending.size - 3]
  have hprevious :
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 3))).result =
      some previous := pendingRunRead_result_of_bounds state _ hlower
  unfold forceCollapseIndexTraced?
  rw [if_pos hmany]
  dsimp only
  have hpositive : 0 < state.pending.size - 2 := by omega
  rw [if_pos hpositive]
  have hlowerEq : state.pending.size - 2 - 1 =
    state.pending.size - 3 := by omega
  have hupperEq : state.pending.size - 2 + 1 =
    state.pending.size - 1 := by omega
  rw [hlowerEq, hupperEq]
  simp only [TraceResult.trace_bind, hprevious,
    TraceResult.trace_pendingRunRead, TraceResult.map, AccessTrace.compose,
    AccessTrace.singletonAccess]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_two_runs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma forceCollapseIndexTraced_two_runs
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
-- given
  (hsize : state.pending.size = 2) :
-- imply
  (forceCollapseIndexTraced? state).result = some 0 ∧ (forceCollapseIndexTraced? state).trace.accesses = [] := by
-- proof
  simp [forceCollapseIndexTraced?, hsize, TraceResult.pure,
    AccessTrace.empty]

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapseLoopTraced_merge_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma mergeForceCollapseLoopTraced_merge_trace_order
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {state : MergeState κ ν}
  {i : Nat}
  {merged : MergeAtResult κ ν}
-- given
  (hmany : 1 < state.pending.size)
  (hindex : (forceCollapseIndexTraced? state).result = some i)
  (hmerge : (mergeAtTraced? state i).result = some merged)
  (hsuccess : merged.returnCode = 0 ∧ !merged.fuelExhausted) :
-- imply
  (mergeForceCollapseLoopTraced? (fuel + 1) state).trace = (forceCollapseIndexTraced? state).trace.compose ((mergeAtTraced? state i).trace.compose (mergeForceCollapseLoopTraced? fuel merged.state).trace) := by
-- proof
  simp only [mergeForceCollapseLoopTraced?, hmany, if_true,
    TraceResult.trace_bind, hindex, hmerge]
  rw [if_pos hsuccess]

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapseLoop_fuel_tracks_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma mergeForceCollapseLoop_fuel_tracks_merge
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {state afterState : MergeState κ ν}
  {before after : List PendingRun}
  {left right merged : PendingRun}
-- given
  (hfuel : fuel + 1 = state.pending.size)
  (hbefore : state.pending.toList = before ++ left :: right :: after)
  (hafter : afterState.pending.toList = before ++ merged :: after) :
-- imply
  fuel = afterState.pending.size := by
-- proof
  have hbeforeSize := congrArg List.length hbefore
  have hafterSize := congrArg List.length hafter
  simp only [Array.length_toList, List.length_append,
    List.length_cons] at hbeforeSize hafterSize
  omega

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapseLoopTraced_singleton_no_access](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma mergeForceCollapseLoopTraced_singleton_no_access
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {state : MergeState κ ν}
-- given
  (hsize : state.pending.size = 1) :
-- imply
  (mergeForceCollapseLoopTraced? (fuel + 1) state).result.map (fun result => (result.returnCode, result.fuelExhausted)) = some (0, false) ∧ (mergeForceCollapseLoopTraced? (fuel + 1) state).trace.accesses = [] ∧ (mergeForceCollapseLoopTraced? (fuel + 1) state).trace.fuelExhausted = false := by
-- proof
  simp [mergeForceCollapseLoopTraced?, hsize,
    mergeForceCollapseSuccessResult, TraceResult.pure, AccessTrace.empty]

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapseTraced_small_no_access](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma mergeForceCollapseTraced_small_no_access
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
-- given
  (hsmall : state.pending.size ≤ 1) :
-- imply
  (mergeForceCollapseTraced? state).result.map (fun result => (result.returnCode, result.fuelExhausted)) = some (0, false) ∧ (mergeForceCollapseTraced? state).trace.accesses = [] ∧ (mergeForceCollapseTraced? state).trace.fuelExhausted = false := by
-- proof
  by_cases hempty : state.pending.size = 0
  · simp [mergeForceCollapseTraced?, hempty,
    mergeForceCollapseLoopTraced?, mergeForceCollapseSuccessResult,
    TraceResult.pure, AccessTrace.empty]
  · have hsingleton : state.pending.size = 1 := by omega
    simpa [mergeForceCollapseTraced?, hsingleton] using
      mergeForceCollapseLoopTraced_singleton_no_access 0 state hsingleton

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeForceCollapseLoopTraced_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma erase_mergeForceCollapseLoopTraced_zero
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  (mergeForceCollapseLoopTraced? 0 state).erase = mergeForceCollapseLoop? 0 state := by
-- proof
  simp only [mergeForceCollapseLoopTraced?, mergeForceCollapseLoop?]
  by_cases hsmall : state.pending.size ≤ 1
  · rw [if_pos hsmall, if_pos hsmall, TraceResult.erase_pure]
    rfl
  · rw [if_neg hsmall, if_neg hsmall,
    TraceResult.erase_markFuelExhausted, TraceResult.erase_pure]
    rfl

end CPythonListsort

namespace CPythonListsort.MergeForceCollapseStableFrame

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma refl
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  MergeForceCollapseStableFrame state state := by
-- proof
  constructor <;> rfl

end CPythonListsort.MergeForceCollapseStableFrame

namespace CPythonListsort.MergeForceCollapseStableFrame

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma trans
  {κ : Type u}
  {ν : Type v}
  {first second third : MergeState κ ν}
-- given
  (hfirst : MergeForceCollapseStableFrame first second)
  (hsecond : MergeForceCollapseStableFrame second third) :
-- imply
  MergeForceCollapseStableFrame first third := by
-- proof
  exact
    { listlen := hsecond.listlen.trans hfirst.listlen
      basekeys := hsecond.basekeys.trans hfirst.basekeys
      dataSize := hsecond.dataSize.trans hfirst.dataSize
      tempValuesMode := hsecond.tempValuesMode.trans hfirst.tempValuesMode
      comparator := hsecond.comparator.trans hfirst.comparator
      mrCurrent := hsecond.mrCurrent.trans hfirst.mrCurrent
      mrE := hsecond.mrE.trans hfirst.mrE
      mrMask := hsecond.mrMask.trans hfirst.mrMask }

end CPythonListsort.MergeForceCollapseStableFrame

namespace CPythonListsort.MergeForceCollapseStableFrame

/--
[of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma of_mergeAt
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
-- given
  (h : MergeAtStableFrame before after) :
-- imply
  MergeForceCollapseStableFrame before after := by
-- proof
  exact
    { listlen := h.listlen
      basekeys := h.basekeys
      dataSize := h.dataSize
      tempValuesMode := h.tempValuesMode
      comparator := h.comparator
      mrCurrent := h.mrCurrent
      mrE := h.mrE
      mrMask := h.mrMask }

end CPythonListsort.MergeForceCollapseStableFrame

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeForceCollapseLoopTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
private lemma mergeForceCollapseLoopTraced_safe
  (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
  (hfuel : fuel = state.pending.size)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hnonempty : state.pending.toList ≠ [])
  (hlayout : PendingLayout state scanned)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
  ∃ result,
    MergeForceCollapseLoopSafetyPost state scanned fuel result := by
  induction fuel generalizing state with
  | zero =>
    have hsizePositive : 0 < state.pending.size := by
      have := List.length_pos_of_ne_nil hnonempty
      simpa using this
    omega
  | succ remaining ih =>
    by_cases hmany : 1 < state.pending.size
    · rcases forceCollapseIndexTraced_safe state hmany with
      ⟨i, hindexResult, hindexSafe, hindexErasure, hposition⟩
      rcases mergeAt_safe state scanned i hlayout hmax hposition hInv hLive
        hMode with ⟨merged, hmerge⟩
      have hmergeSafe : MovementTraceSafe (mergeAtTraced? state i) :=
        ⟨hmerge.traceFuel, hmerge.noPushes, hmerge.accessesInBounds,
          hmerge.tempAccessesLive⟩
      have hmergeRaw : mergeAt? state i = some merged := by
        rwa [← hmerge.exactErasure]
      rcases mergeAt_preserves_pendingLayout state scanned i merged hlayout
        hmergeRaw with
        ⟨before, left, right, after, hbeforeLength, hbeforePending,
          hafterPending, _hleftNonnegative, _hleftPositive,
          _hrightNonnegative, _hrightPositive, _hadjacent, _hsum,
          hmergedLayout⟩
      have hnextFuel : remaining = merged.state.pending.size :=
        mergeForceCollapseLoop_fuel_tracks_merge remaining state
          merged.state before after left right
          ({ left with len := left.len + right.len } : PendingRun)
          hfuel hbeforePending hafterPending
      have hmergedNonempty : merged.state.pending.toList ≠ [] := by
        rw [hafterPending]
        simp
      have hmergedMax : merged.state.listlen.toNat ≤ PY_LIST_MAX := by
        rwa [hmerge.stableFrame.listlen]
      rcases ih merged.state hnextFuel hmergedMax hmergedNonempty
        hmergedLayout hmerge.tempInvariant hmerge.tempLive
        hmerge.valuesMode with ⟨result, hrest⟩
      have hsuccess :
        merged.returnCode = 0 ∧ !merged.fuelExhausted := by
        exact ⟨hmerge.returnCode, by simp [hmerge.resultFuel]⟩
      have htailSafe : MovementTraceSafe
        ((mergeAtTraced? state i).bind fun merged =>
          if merged.returnCode = 0 ∧ !merged.fuelExhausted then
            mergeForceCollapseLoopTraced? remaining merged.state
          else
            TraceResult.pure
              (mergeForceCollapseFromMergeAt merged)) := by
        apply MovementTraceSafe.bind _ _ merged hmerge.resultEq hmergeSafe
        rwa [if_pos hsuccess]
      have hfullSafe : MovementTraceSafe
        (mergeForceCollapseLoopTraced? (remaining + 1) state) := by
        simp only [mergeForceCollapseLoopTraced?, hmany, if_true]
        exact MovementTraceSafe.bind _ _ i hindexResult hindexSafe htailSafe
      have hresult :
        (mergeForceCollapseLoopTraced? (remaining + 1) state).result =
          some result := by
        simp only [mergeForceCollapseLoopTraced?, hmany, if_true]
        rw [TraceResult.bind_result_of_eq_some _ _ i hindexResult]
        rw [TraceResult.bind_result_of_eq_some _ _ merged hmerge.resultEq]
        rwa [if_pos hsuccess]
      have hexact :
        (mergeForceCollapseLoopTraced? (remaining + 1) state).erase =
          mergeForceCollapseLoop? (remaining + 1) state := by
        simp only [mergeForceCollapseLoopTraced?, mergeForceCollapseLoop?,
          hmany, if_true, TraceResult.erase_bind]
        rw [hindexErasure]
        have hindexRaw : forceCollapseIndex? state = some i := by
          rwa [← hindexErasure]
        rw [hindexRaw]
        simp only [Option.bind_some]
        rw [hmerge.exactErasure, hmergeRaw]
        simp only [Option.bind_some, if_pos hsuccess]
        exact hrest.exactErasure
      have htraceOrder :
        (mergeForceCollapseLoopTraced? (remaining + 1) state).trace =
          (forceCollapseIndexTraced? state).trace.compose
            ((mergeAtTraced? state i).trace.compose
              (mergeForceCollapseLoopTraced? remaining
                merged.state).trace) :=
        mergeForceCollapseLoopTraced_merge_trace_order remaining state i
          merged hmany hindexResult hmerge.resultEq hsuccess
      refine ⟨result, ?_⟩
      exact
        { resultEq := hresult
          returnCode := hrest.returnCode
          resultFuel := hrest.resultFuel
          traceSafe := hfullSafe
          exactErasure := hexact
          tempInvariant := hrest.tempInvariant
          tempLive := hrest.tempLive
          valuesMode := hrest.valuesMode
          hasValuesFrame := hrest.hasValuesFrame.trans
            hmerge.hasValuesFrame
          memoryEventsValid := by
            rw [htraceOrder,
              AccessTrace.memoryEventsValid_compose,
              AccessTrace.memoryEventsValid_compose]
            refine ⟨?_, hmerge.memoryEventsValid, ?_⟩
            · simp [AccessTrace.memoryEventsValid,
              forceCollapseIndexTraced_memoryEvents_eq_nil]
            · simpa [hmerge.hasValuesFrame] using
              hrest.memoryEventsValid
          onlyMergeMemoryEvents := by
            rw [htraceOrder,
              AccessTrace.onlyMergeMemoryEvents_compose,
              AccessTrace.onlyMergeMemoryEvents_compose]
            refine ⟨?_, hmerge.onlyMergeMemoryEvents,
              hrest.onlyMergeMemoryEvents⟩
            simp [AccessTrace.onlyMergeMemoryEvents,
              forceCollapseIndexTraced_memoryEvents_eq_nil]
          memoryEventsBounded := by
            intro hbound
            rw [htraceOrder,
              AccessTrace.mergeMemoryEventsBounded_compose,
              AccessTrace.mergeMemoryEventsBounded_compose]
            refine ⟨?_, hmerge.memoryEventsBounded hbound, ?_⟩
            · simp [AccessTrace.mergeMemoryEventsBounded,
              forceCollapseIndexTraced_memoryEvents_eq_nil]
            · exact hrest.memoryEventsBounded
              (hmerge.physicalSlotsBound hbound)
          physicalSlotsBound := by
            intro hbound
            exact hrest.physicalSlotsBound
              (hmerge.physicalSlotsBound hbound)
          memorySegment := by
            rw [htraceOrder]
            exact AccessTrace.mergeMemorySegment_compose _ _ _ _ _
              (forceCollapseIndexTraced_memorySegment state)
              (AccessTrace.mergeMemorySegment_compose _ _ _ _ _
                hmerge.memorySegment hrest.memorySegment)
          stableFrame :=
            (MergeForceCollapseStableFrame.of_mergeAt hmerge.stableFrame).trans
              hrest.stableFrame
          pendingLayout := hrest.pendingLayout
          singleton := hrest.singleton }
    · have hsizeOne : state.pending.size = 1 := by
      have hsizePositive : 0 < state.pending.size := by
        have := List.length_pos_of_ne_nil hnonempty
        simpa using this
      omega
      have hlistLength : state.pending.toList.length = 1 := by
        simpa only [Array.length_toList] using hsizeOne
      obtain ⟨run, hruns⟩ := List.length_eq_one_iff.mp hlistLength
      let result := mergeForceCollapseSuccessResult state
      have hpure : MovementTraceSafe (TraceResult.pure result) :=
        MovementTraceSafe.pure result
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
          simp only [mergeForceCollapseLoopTraced?, hmany, if_false]
          change (TraceResult.pure result).result = some result
          rfl
          returnCode := rfl
          resultFuel := rfl
          traceSafe := by
            simpa [mergeForceCollapseLoopTraced?, hmany, result] using hpure
          exactErasure := by
            simp only [mergeForceCollapseLoopTraced?,
              mergeForceCollapseLoop?, hmany, if_false,
              TraceResult.erase_pure]
            rfl
          tempInvariant := hInv
          tempLive := hLive
          valuesMode := hMode
          hasValuesFrame := rfl
          memoryEventsValid := by
            simp [mergeForceCollapseLoopTraced?, hmany,
              AccessTrace.memoryEventsValid, TraceResult.pure,
              AccessTrace.empty]
          onlyMergeMemoryEvents := by
            simp [mergeForceCollapseLoopTraced?, hmany,
              AccessTrace.onlyMergeMemoryEvents, TraceResult.pure,
              AccessTrace.empty]
          memoryEventsBounded := by
            intro _
            simp [mergeForceCollapseLoopTraced?, hmany,
              AccessTrace.mergeMemoryEventsBounded, TraceResult.pure,
              AccessTrace.empty]
          physicalSlotsBound := fun hbound => hbound
          memorySegment := by
            refine ⟨[], ?_, ?_⟩
            · simp [mergeForceCollapseLoopTraced?, hmany,
              TraceResult.pure, AccessTrace.empty]
            · rfl
          stableFrame := MergeForceCollapseStableFrame.refl state
          pendingLayout := hlayout
          singleton := ⟨run, hruns⟩ }

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapse_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma mergeForceCollapse_safe
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned : Nat}
-- given
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hnonempty : state.pending.toList ≠ [])
  (hlayout : PendingLayout state scanned)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
-- imply
  ∃ result, MergeForceCollapseSafetyPost state scanned result := by
-- proof
  rcases mergeForceCollapseLoopTraced_safe state.pending.size state scanned rfl
    hmax hnonempty hlayout hInv hLive hMode with ⟨result, hresult⟩
  have hraw : mergeForceCollapse? state = some result := by
    unfold mergeForceCollapse?
    rwa [← hresult.exactErasure]
  rcases mergeForceCollapse_preserves_pendingLayout state scanned result
    hnonempty hlayout hraw hresult.returnCode hresult.resultFuel with
    ⟨_hlistlen, _hbasekeys, _hdataSize, _hresultLayout, run,
      hpending, hbase, hend⟩
  refine ⟨result, ?_⟩
  exact
    { resultEq := hresult.resultEq
      returnCode := hresult.returnCode
      resultFuel := hresult.resultFuel
      traceFuel := hresult.traceSafe.fuel
      accessesInBounds := hresult.traceSafe.bounds
      tempAccessesLive := hresult.traceSafe.tempLive
      noPushes := hresult.traceSafe.noPushes
      exactErasure := hresult.exactErasure
      tempInvariant := hresult.tempInvariant
      tempLive := hresult.tempLive
      valuesMode := hresult.valuesMode
      hasValuesFrame := hresult.hasValuesFrame
      memoryEventsValid := hresult.memoryEventsValid
      onlyMergeMemoryEvents := hresult.onlyMergeMemoryEvents
      memoryEventsBounded := hresult.memoryEventsBounded
      physicalSlotsBound := hresult.physicalSlotsBound
      memorySegment := hresult.memorySegment
      stableFrame := hresult.stableFrame
      pendingLayout := hresult.pendingLayout
      singleton := hresult.singleton
      finalRun := ⟨run, hpending, hbase, hend⟩ }

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeForceCollapseTraced_of_admitted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma erase_mergeForceCollapseTraced_of_admitted
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned : Nat}
-- given
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hnonempty : state.pending.toList ≠ [])
  (hlayout : PendingLayout state scanned)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
-- imply
  (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state := by
-- proof
  rcases mergeForceCollapse_safe state scanned hmax hnonempty hlayout hInv
    hLive hMode with ⟨_result, hresult⟩
  exact hresult.exactErasure

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_two_run_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma forceCollapseIndexTraced_two_run_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  forceCollapseIndexTraced? forceCollapseTwoRegressionState = { result := some 0, trace := AccessTrace.empty } := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_empty_failure_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma forceCollapseIndexTraced_empty_failure_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  forceCollapseIndexTraced? forceCollapseEmptyRegressionState = { result := none, trace := AccessTrace.empty } ∧ forceCollapseIndex? forceCollapseEmptyRegressionState = none := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_lower_branch_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma forceCollapseIndexTraced_lower_branch_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  forceCollapseIndexTraced? forceCollapseLowerRegressionState = { result := some 0 trace := { accesses := [{ kind := .read, region := .pendingRuns, index := 0, extent := 3 }, { kind := .read, region := .pendingRuns, index := 2, extent := 3 }] pushDepths := [] fuelExhausted := false } } := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_tie_chooses_top_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma forceCollapseIndexTraced_tie_chooses_top_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  forceCollapseIndexTraced? forceCollapseTieRegressionState = { result := some 1 trace := { accesses := [{ kind := .read, region := .pendingRuns, index := 0, extent := 3 }, { kind := .read, region := .pendingRuns, index := 2, extent := 3 }] pushDepths := [] fuelExhausted := false } } := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapseLoopTraced_zero_fuel_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma mergeForceCollapseLoopTraced_zero_fuel_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (mergeForceCollapseLoopTraced? 0 forceCollapseTieRegressionState).result.map (fun result => (result.returnCode, result.fuelExhausted)) = some (-1, true) ∧ (mergeForceCollapseLoopTraced? 0 forceCollapseTieRegressionState).trace.fuelExhausted = true ∧ (mergeForceCollapseLoopTraced? 0 forceCollapseTieRegressionState).erase = mergeForceCollapseLoop? 0 forceCollapseTieRegressionState := by
-- proof
  constructor
  · decide
  constructor
  · decide
  · exact erase_mergeForceCollapseLoopTraced_zero _

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapseLoopTraced_delegated_failure_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean)
-/
@[path]
lemma mergeForceCollapseLoopTraced_delegated_failure_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (mergeForceCollapseLoopTraced? 1 forceCollapseRejectedMergeState).result = none ∧ (mergeForceCollapseLoopTraced? 1 forceCollapseRejectedMergeState).trace.accesses = [{ kind := .read, region := .pendingRuns, index := 0, extent := 2 }, { kind := .read, region := .pendingRuns, index := 1, extent := 2 }] ∧ (mergeForceCollapseLoopTraced? 1 forceCollapseRejectedMergeState).trace.fuelExhausted = false := by
-- proof
  decide

end CPythonListsort


-- created on 2026-10-23
