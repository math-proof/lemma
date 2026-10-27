import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.FoundNewRunSafety.Part2
open CPythonListsort CPythonListsort.FoundNewRunStableFrame


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[bind_result_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
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
[pendingRunRead_result_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
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
[pendingRunRead_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
private lemma pendingRunRead_safe (state : MergeState κ ν) (index : Int)
  (hindex : 0 ≤ index ∧ index.toNat < state.pending.size) :
  MovementTraceSafe (TraceResult.pendingRunRead? state index) := by
  constructor
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_pendingRunRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds] using
        (show 0 ≤ index ∧ index < Int.ofNat state.pending.size from
          ⟨hindex.1, (Int.toNat_lt hindex.1).mp hindex.2⟩)
  · simp [TraceResult.trace_pendingRunRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[pendingRunPowerWrite_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
private lemma pendingRunPowerWrite_safe (state : MergeState κ ν)
  (index : Int) (power : Nat)
  (hindex : 0 ≤ index ∧ index.toNat < state.pending.size) :
  MovementTraceSafe
    (TraceResult.pendingRunPowerWrite? state index power) := by
  constructor
  · simp [TraceResult.trace_pendingRunPowerWrite,
    AccessTrace.singletonAccess]
  · simp [TraceResult.trace_pendingRunPowerWrite,
    AccessTrace.singletonAccess]
  · rw [TraceResult.trace_pendingRunPowerWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds] using
        (show 0 ≤ index ∧ index < Int.ofNat state.pending.size from
          ⟨hindex.1, (Int.toNat_lt hindex.1).mp hindex.2⟩)
  · simp [TraceResult.trace_pendingRunPowerWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[pendingRunPowerWrite_result_of_lookup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
private lemma pendingRunPowerWrite_result_of_lookup
  (state : MergeState κ ν) (index power : Nat) (top : PendingRun)
  (hlookup : state.pending[index]? = some top) :
  (TraceResult.pendingRunPowerWrite? state (Int.ofNat index) power).result =
    some
      { state with
        pending := state.pending.setIfInBounds index
          ({ top with power := some power } : PendingRun) } := by
  change
    (TraceResult.pendingRunPowerWrite? state (Int.ofNat index) power).erase = _
  rw [TraceResult.erase_pendingRunPowerWrite]
  have hnonnegative : 0 ≤ Int.ofNat index := Int.natCast_nonneg _
  rw [if_pos hnonnegative]
  have htoi : (Int.ofNat index).toNat = index := rfl
  rw [htoi]
  simp [hlookup]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[pySSize_slt_zero_of_nonnegative_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
private lemma pySSize_slt_zero_of_nonnegative_positive (x : PySSize)
  (hnonnegative : x.Nonnegative) (hpositive : 0 < x.toNat) :
  (0 : PySSize).slt x := by
  rw [BitVec.slt_eq_decide, decide_eq_true_eq]
  rw [BitVec.toInt_eq_toNat_of_msb hnonnegative]
  norm_num [BitVec.toInt_ofNat]
  exact_mod_cast hpositive

end CPythonListsort

namespace CPythonListsort.FoundNewRunStableFrame

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma refl
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  FoundNewRunStableFrame state state := by
-- proof
  constructor <;> rfl

end CPythonListsort.FoundNewRunStableFrame

namespace CPythonListsort.FoundNewRunStableFrame

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma trans
  {κ : Type u}
  {ν : Type v}
  {first second third : MergeState κ ν}
-- given
  (hfirst : FoundNewRunStableFrame first second)
  (hsecond : FoundNewRunStableFrame second third) :
-- imply
  FoundNewRunStableFrame first third := by
-- proof
  constructor
  · exact hsecond.listlen.trans hfirst.listlen
  · exact hsecond.basekeys.trans hfirst.basekeys
  · exact hsecond.dataSize.trans hfirst.dataSize
  · exact hsecond.tempValuesMode.trans hfirst.tempValuesMode
  · exact hsecond.comparator.trans hfirst.comparator
  · exact hsecond.mrCurrent.trans hfirst.mrCurrent
  · exact hsecond.mrE.trans hfirst.mrE
  · exact hsecond.mrMask.trans hfirst.mrMask

end CPythonListsort.FoundNewRunStableFrame

namespace CPythonListsort.FoundNewRunStableFrame

/--
[of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma of_mergeAt
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
-- given
  (h : MergeAtStableFrame before after) :
-- imply
  FoundNewRunStableFrame before after := by
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

end CPythonListsort.FoundNewRunStableFrame

namespace CPythonListsort

/--
[erase_setTopPowerTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma erase_setTopPowerTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {power : Nat} :
-- imply
  (setTopPowerTraced? state power).erase = setTopPower? state power := by
-- proof
  unfold setTopPowerTraced? setTopPower?
  split
  · rfl
  · rw [TraceResult.erase_pendingRunPowerWrite]
    have hnonnegative :
      0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi :
      (Int.ofNat (state.pending.size - 1)).toNat =
        state.pending.size - 1 := rfl
    rw [htoi]
    generalize hlookup : state.pending[state.pending.size - 1]? = lookup
    cases lookup <;> simp [Option.map, hlookup]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[setTopPowerTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
event: it either performs one pending-record write or returns an empty trace. -/
private lemma setTopPowerTraced_memoryEvents_eq_nil
  (state : MergeState κ ν) (power : Nat) :
  (setTopPowerTraced? state power).trace.memoryEvents = [] := by
  unfold setTopPowerTraced?
  split <;> simp [TraceResult.failure,
    TraceResult.trace_pendingRunPowerWrite, AccessTrace.singletonAccess,
    AccessTrace.empty]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[setTopPowerTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
private lemma setTopPowerTraced_safe (state : MergeState κ ν)
  (power : Nat) (hnonempty : state.pending.toList ≠ []) :
  ∃ after, SetTopPowerSafetyPost state power after := by
  have hsizePositive : 0 < state.pending.size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hnonempty
    apply List.eq_nil_of_length_eq_zero
    simpa using hzero
  let index := state.pending.size - 1
  have hindex : index < state.pending.size := by
    dsimp [index]
    omega
  let top := state.pending[index]
  have hlookup : state.pending[index]? = some top := by
    exact Array.getElem?_eq_getElem hindex
  let after : MergeState κ ν :=
    { state with
      pending := state.pending.setIfInBounds index
        ({ top with power := some power } : PendingRun) }
  have hwriteResult :
    (TraceResult.pendingRunPowerWrite? state (Int.ofNat index) power).result =
      some after := by
    simpa [after] using
      pendingRunPowerWrite_result_of_lookup state index power top hlookup
  have hwriteSafe : MovementTraceSafe
    (TraceResult.pendingRunPowerWrite? state (Int.ofNat index) power) :=
    pendingRunPowerWrite_safe state (Int.ofNat index) power
      ⟨Int.natCast_nonneg _, by simpa using hindex⟩
  refine ⟨after, ?_⟩
  constructor
  · unfold setTopPowerTraced?
    rw [if_neg]
    · exact hwriteResult
    · simpa [Array.isEmpty_iff_size_eq_zero] using ne_of_gt hsizePositive
  · unfold setTopPowerTraced?
    rw [if_neg]
    · exact hwriteSafe
    · simpa [Array.isEmpty_iff_size_eq_zero] using ne_of_gt hsizePositive
  · exact erase_setTopPowerTraced state power
  · constructor <;> rfl
  · rfl
  · rfl
  · rfl
  · simp [after]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[newRun_not_mem_of_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
private lemma newRun_not_mem_of_layout
  {state : MergeState κ ν} {scanned : Nat} {newRun : PendingRun}
  (hlayout : PendingLayout state scanned)
  (hnewBase : newRun.base = state.basekeys + scanned) :
  newRun ∉ state.pending.toList := by
  intro hmember
  have hspec := hlayout.2.2.2.member_spec hmember
  have hbaseLt : newRun.base < state.basekeys + scanned := by
    simp only [PendingRun.endIndex] at hspec
    omega
  rw [hnewBase] at hbaseLt
  omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[foundNewRunLoopTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
private lemma foundNewRunLoopTraced_safe
  (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
  (before : List PendingRun) (top newRun : PendingRun) (power : Nat)
  (hfuel : fuel = state.pending.size)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hsplit : state.pending.toList = before ++ [top])
  (hnewBase : newRun.base = state.basekeys + scanned)
  (hnewNonnegative : newRun.len.Nonnegative)
  (hnewPositive : 0 < newRun.len.toNat)
  (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
  (hpower : power =
    pendingBoundaryPower state.basekeys state.listlen top newRun)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
  ∃ result, FoundNewRunLoopSafetyPost state scanned fuel power result := by
  induction fuel generalizing state before top with
  | zero =>
    have hsizePositive : 0 < state.pending.size := by
      have hlength := congrArg List.length hsplit
      simp only [Array.length_toList, List.length_append,
        List.length_singleton] at hlength
      omega
    omega
  | succ remaining ih =>
    have hsize : state.pending.size = before.length + 1 := by
      have hlength := congrArg List.length hsplit
      simpa using hlength
    by_cases hmany : 1 < state.pending.size
    · rcases List.eq_nil_or_concat' before with hbeforeEmpty |
      ⟨older, preceding, hbefore⟩
      · subst before
        simp at hsize
        omega
      · have hindex : state.pending.size - 2 < state.pending.size := by
        omega
        have hlookup :
          state.pending[state.pending.size - 2]? = some preceding := by
          rw [← Array.getElem?_toList, hsplit, hbefore, hsize]
          simp [hbefore]
        have hreadResult :
          (TraceResult.pendingRunRead? state
            (Int.ofNat (state.pending.size - 2))).result =
              some preceding := by
          have hget : state.pending[state.pending.size - 2] = preceding := by
            rw [Array.getElem?_eq_getElem hindex] at hlookup
            exact Option.some.inj hlookup
          rw [pendingRunRead_result_of_bounds state
            (state.pending.size - 2) hindex, hget]
        have hreadSafe : MovementTraceSafe
          (TraceResult.pendingRunRead? state
            (Int.ofNat (state.pending.size - 2))) :=
          pendingRunRead_safe state _
            ⟨Int.natCast_nonneg _, by simpa using hindex⟩
        have hprecedingPower : preceding.power = some
          (pendingBoundaryPower state.basekeys state.listlen
            preceding top) := by
          apply hpowered.boundary_power (before := older) (after := [])
          simpa [hbefore, List.append_assoc] using hsplit
        let precedingPower :=
          pendingBoundaryPower state.basekeys state.listlen preceding top
        by_cases hguard : power < precedingPower
        · rcases mergeAt_safe state scanned (state.pending.size - 2)
          hlayout hmax (Or.inl (by omega)) hInv hLive hMode with
          ⟨merged, hmerge⟩
          have hmergeSafe : MovementTraceSafe
            (mergeAtTraced? state (state.pending.size - 2)) :=
            ⟨hmerge.traceFuel, hmerge.noPushes, hmerge.accessesInBounds,
              hmerge.tempAccessesLive⟩
          have hmergeRaw :
            mergeAt? state (state.pending.size - 2) = some merged := by
            rwa [← hmerge.exactErasure]
          have hmergeSuccess :
            merged.returnCode = 0 ∧ !merged.fuelExhausted := by
            exact ⟨hmerge.returnCode, by simp [hmerge.resultFuel]⟩
          have houtside : newRun ∉ state.pending.toList :=
            newRun_not_mem_of_layout hlayout hnewBase
          have hpolicy := mergeTop_preserves_poweredPrefix
            state scanned older preceding top newRun precedingPower power
            merged hmax hlayout hpowered
            (by simpa [hbefore, List.append_assoc] using hsplit)
            hnewBase hnewNonnegative hnewPositive hnewWithin houtside
            (by simpa [precedingPower] using hprecedingPower) rfl hpower
            hguard hmergeRaw hmerge.returnCode hmerge.resultFuel
          let mergedTop : PendingRun :=
            { preceding with len := preceding.len + top.len }
          have hmergedSplit : merged.state.pending.toList =
            older ++ [mergedTop] := by
            simpa [mergedTop] using hpolicy.1
          have hmergedPowered : PoweredPrefix merged.state :=
            hpolicy.2.2.2.1
          have hmergedPower : power = pendingBoundaryPower
            merged.state.basekeys merged.state.listlen mergedTop newRun := by
            simpa [mergedTop] using hpolicy.2.2.2.2
          have hremaining : remaining = merged.state.pending.size := by
            have hmergedLength := congrArg List.length hmergedSplit
            simp only [Array.length_toList, List.length_append,
              List.length_singleton] at hmergedLength
            rw [hbefore] at hsize
            simp only [List.length_append, List.length_singleton] at hsize
            omega
          have hmergedMax :
            merged.state.listlen.toNat ≤ PY_LIST_MAX := by
            rwa [hmerge.stableFrame.listlen]
          have hmergedNewBase :
            newRun.base = merged.state.basekeys + scanned := by
            rwa [hmerge.stableFrame.basekeys]
          have hmergedNewWithin :
            scanned + newRun.len.toNat ≤ merged.state.listlen.toNat := by
            rwa [hmerge.stableFrame.listlen]
          rcases ih merged.state older mergedTop hremaining hmergedMax
            hmerge.pendingLayout hmergedPowered hmergedSplit
            hmergedNewBase hmergedNewWithin hmergedPower
            hmerge.tempInvariant hmerge.tempLive hmerge.valuesMode with
            ⟨result, hresult⟩
          have hmemoryEvents :
            (foundNewRunLoopTraced? (remaining + 1) state power).trace.memoryEvents =
              (mergeAtTraced? state (state.pending.size - 2)).trace.memoryEvents ++
                (foundNewRunLoopTraced? remaining merged.state power).trace.memoryEvents := by
            simp only [foundNewRunLoopTraced?, hmany, if_pos,
              TraceResult.trace_bind, hreadResult]
            simp only [hprecedingPower]
            rw [if_pos (by simpa [precedingPower] using hguard)]
            simp only [TraceResult.trace_bind, hmerge.resultEq]
            rw [if_pos hmergeSuccess]
            simp [AccessTrace.memoryEvents_compose,
              TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
          refine ⟨result, ?_⟩
          constructor
          · simp only [foundNewRunLoopTraced?, hmany, if_pos]
            rw [TraceResult.bind_result_of_eq_some _ _ preceding hreadResult]
            simp only [hprecedingPower]
            rw [if_pos (by simpa [precedingPower] using hguard)]
            rw [TraceResult.bind_result_of_eq_some _ _ merged
              hmerge.resultEq]
            rwa [if_pos hmergeSuccess]
          · exact hresult.returnCode
          · exact hresult.resultFuel
          · simp only [foundNewRunLoopTraced?, hmany, if_pos]
            apply MovementTraceSafe.bind _ _ preceding hreadResult hreadSafe
            simp only [hprecedingPower]
            rw [if_pos (by simpa [precedingPower] using hguard)]
            apply MovementTraceSafe.bind _ _ merged hmerge.resultEq
              hmergeSafe
            rwa [if_pos hmergeSuccess]
          · simp only [foundNewRunLoopTraced?, foundNewRunLoop?, hmany,
            if_pos, TraceResult.erase_bind,
            TraceResult.erase_pendingRunRead]
            have hnonnegative :
              0 ≤ Int.ofNat (state.pending.size - 2) :=
              Int.natCast_nonneg _
            rw [if_pos hnonnegative]
            have htoi :
              (Int.ofNat (state.pending.size - 2)).toNat =
                state.pending.size - 2 := rfl
            rw [htoi, hlookup]
            simp only [Option.bind_some]
            rw [hprecedingPower]
            simp only
            have hguard' : power < pendingBoundaryPower state.basekeys
              state.listlen preceding top := by
              exact hguard
            simp only [if_pos hguard', TraceResult.erase_bind]
            rw [hmerge.exactErasure, hmergeRaw]
            simp only [Option.bind_some, if_pos hmergeSuccess]
            exact hresult.exactErasure
          · exact hresult.tempInvariant
          · exact hresult.tempLive
          · exact hresult.valuesMode
          · exact hresult.hasValuesFrame.trans hmerge.hasValuesFrame
          · exact (FoundNewRunStableFrame.of_mergeAt hmerge.stableFrame).trans
            hresult.stableFrame
          · intro event hevent
            rw [hmemoryEvents] at hevent
            obtain hcall | hrest := List.mem_append.mp hevent
            · exact hmerge.memoryEventsValid event hcall
            · have hvalid := hresult.memoryEventsValid event hrest
              rwa [hmerge.hasValuesFrame] at hvalid
          · intro event hevent
            rw [hmemoryEvents] at hevent
            obtain hcall | hrest := List.mem_append.mp hevent
            · exact hmerge.onlyMergeMemoryEvents event hcall
            · exact hresult.onlyMergeMemoryEvents event hrest
          · intro hbound event hevent
            rw [hmemoryEvents] at hevent
            obtain hcall | hrest := List.mem_append.mp hevent
            · exact hmerge.memoryEventsBounded hbound event hcall
            · exact hresult.memoryEventsBounded
              (hmerge.physicalSlotsBound hbound) event hrest
          · intro hbound
            exact hresult.physicalSlotsBound
              (hmerge.physicalSlotsBound hbound)
          · rcases hmerge.memorySegment with
            ⟨mergeCalls, hmergeEvents, hmergeChain⟩
            rcases hresult.memorySegment with
              ⟨restCalls, hrestEvents, hrestChain⟩
            refine ⟨mergeCalls ++ restCalls, ?_,
              AccessTrace.MergeMemoryCallChain.append hmergeChain hrestChain⟩
            rw [hmemoryEvents, hmergeEvents, hrestEvents]
            simp [List.map_append]
        · rcases setTopPowerTraced_safe state power
          (by simp [hsplit]) with ⟨after, hset⟩
          let result := foundNewRunSuccessResult after
          have hsetRaw : setTopPower? state power = some after := by
            rwa [← hset.exactErasure]
          have hmemoryEvents :
            (foundNewRunLoopTraced? (remaining + 1) state power).trace.memoryEvents = [] := by
            simp only [foundNewRunLoopTraced?, hmany, if_pos,
              TraceResult.trace_bind, hreadResult]
            simp only [hprecedingPower]
            rw [if_neg (by simpa [precedingPower] using hguard)]
            simp [TraceResult.memoryEvents_map,
              AccessTrace.memoryEvents_compose,
              TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess,
              setTopPowerTraced_memoryEvents_eq_nil]
          refine ⟨result, ?_⟩
          constructor
          · simp only [foundNewRunLoopTraced?, hmany, if_pos]
            rw [TraceResult.bind_result_of_eq_some _ _ preceding hreadResult]
            simp only [hprecedingPower]
            rw [if_neg (by simpa [precedingPower] using hguard)]
            change Option.map foundNewRunSuccessResult
              (setTopPowerTraced? state power).result = some result
            rw [hset.resultEq]
            rfl
          · rfl
          · rfl
          · simp only [foundNewRunLoopTraced?, hmany, if_pos]
            apply MovementTraceSafe.bind _ _ preceding hreadResult hreadSafe
            simp only [hprecedingPower]
            rw [if_neg (by simpa [precedingPower] using hguard)]
            exact MovementTraceSafe.map _ _ hset.traceSafe
          · simp only [foundNewRunLoopTraced?, foundNewRunLoop?, hmany,
            if_pos, TraceResult.erase_bind,
            TraceResult.erase_pendingRunRead]
            have hnonnegative :
              0 ≤ Int.ofNat (state.pending.size - 2) :=
              Int.natCast_nonneg _
            rw [if_pos hnonnegative]
            have htoi :
              (Int.ofNat (state.pending.size - 2)).toNat =
                state.pending.size - 2 := rfl
            rw [htoi, hlookup]
            simp only [Option.bind_some]
            rw [hprecedingPower]
            simp only
            have hguard' : ¬power < pendingBoundaryPower state.basekeys
              state.listlen preceding top := by
              exact hguard
            simp only [if_neg hguard', TraceResult.erase_map]
            rw [hset.exactErasure, hsetRaw]
            simp [foundNewRunSuccessResult]
          · change TempStorageInv after.a after.alloced
            rwa [hset.storageEq, hset.allocedEq]
          · change after.a.Live
            rwa [hset.storageEq]
          · change SortSlice.ValuesModeInvariant after.a.hasValues after.data
            rwa [hset.storageEq, hset.dataEq]
          · change after.a.hasValues = state.a.hasValues
            exact congrArg TempStorage.hasValues hset.storageEq
          · change FoundNewRunStableFrame state after
            exact hset.stableFrame
          · simp [AccessTrace.memoryEventsValid, hmemoryEvents]
          · simp [AccessTrace.onlyMergeMemoryEvents, hmemoryEvents]
          · intro _
            simp [AccessTrace.mergeMemoryEventsBounded, hmemoryEvents]
          · intro hbound
            change (MergeMemorySnapshot.ofState after).PhysicalBound
            simpa [MergeMemorySnapshot.PhysicalBound,
              MergeMemorySnapshot.ofState, hset.storageEq] using hbound
          · refine ⟨[], hmemoryEvents, ?_⟩
            rw [AccessTrace.MergeMemoryCallChain.nil_iff]
            simp [result, foundNewRunSuccessResult,
              MergeMemorySnapshot.ofState, hset.storageEq,
              hset.allocedEq, hset.dataEq]
    · rcases setTopPowerTraced_safe state power
      (by simp [hsplit]) with ⟨after, hset⟩
      let result := foundNewRunSuccessResult after
      have hsetRaw : setTopPower? state power = some after := by
        rwa [← hset.exactErasure]
      have hmemoryEvents :
        (foundNewRunLoopTraced? (remaining + 1) state power).trace.memoryEvents = [] := by
        simp only [foundNewRunLoopTraced?, hmany, if_false,
          TraceResult.memoryEvents_map]
        exact setTopPowerTraced_memoryEvents_eq_nil state power
      refine ⟨result, ?_⟩
      constructor
      · simp only [foundNewRunLoopTraced?, hmany, if_false]
        change Option.map foundNewRunSuccessResult
          (setTopPowerTraced? state power).result = some result
        rw [hset.resultEq]
        rfl
      · rfl
      · rfl
      · simp only [foundNewRunLoopTraced?, hmany, if_false]
        exact MovementTraceSafe.map _ _ hset.traceSafe
      · simp only [foundNewRunLoopTraced?, foundNewRunLoop?, hmany,
        if_false, TraceResult.erase_map]
        simp [hset.exactErasure, hsetRaw, foundNewRunSuccessResult]
      · change TempStorageInv after.a after.alloced
        rwa [hset.storageEq, hset.allocedEq]
      · change after.a.Live
        rwa [hset.storageEq]
      · change SortSlice.ValuesModeInvariant after.a.hasValues after.data
        rwa [hset.storageEq, hset.dataEq]
      · change after.a.hasValues = state.a.hasValues
        exact congrArg TempStorage.hasValues hset.storageEq
      · change FoundNewRunStableFrame state after
        exact hset.stableFrame
      · simp [AccessTrace.memoryEventsValid, hmemoryEvents]
      · simp [AccessTrace.onlyMergeMemoryEvents, hmemoryEvents]
      · intro _
        simp [AccessTrace.mergeMemoryEventsBounded, hmemoryEvents]
      · intro hbound
        change (MergeMemorySnapshot.ofState after).PhysicalBound
        simpa [MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState, hset.storageEq] using hbound
      · refine ⟨[], hmemoryEvents, ?_⟩
        rw [AccessTrace.MergeMemoryCallChain.nil_iff]
        simp [result, foundNewRunSuccessResult,
          MergeMemorySnapshot.ofState, hset.storageEq,
          hset.allocedEq, hset.dataEq]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[foundNewRun_safe_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
private lemma foundNewRun_safe_core
  (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hnewBase : newRun.base = state.basekeys + scanned)
  (hnewNonnegative : newRun.len.Nonnegative)
  (hnewPositive : 0 < newRun.len.toNat)
  (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
  ∃ result, FoundNewRunSafetyPost state scanned newRun result := by
  by_cases hempty : state.pending.isEmpty = true
  · let result := foundNewRunSuccessResult state
    have hresult :
      (foundNewRunTraced? state newRun.len.toNat).result = some result := by
      unfold foundNewRunTraced?
      rw [if_pos hempty]
      rfl
    have hexact :
      (foundNewRunTraced? state newRun.len.toNat).erase =
        foundNewRun? state newRun.len.toNat := by
      simp [foundNewRunTraced?, foundNewRun?, hempty,
        foundNewRunSuccessResult]
    have hraw : foundNewRun? state newRun.len.toNat = some result := by
      rwa [← hexact]
    have houtside : newRun ∉ state.pending.toList :=
      newRun_not_mem_of_layout hlayout hnewBase
    have hready := foundNewRun_preserves_readyToPush state scanned newRun
      result hmax hlayout hpowered hnewBase hnewNonnegative hnewPositive
      hnewWithin houtside hraw rfl rfl
    have hpure : MovementTraceSafe
      (TraceResult.pure (foundNewRunSuccessResult state)) :=
      MovementTraceSafe.pure _
    have hmemoryEvents :
      (foundNewRunTraced? state newRun.len.toNat).trace.memoryEvents = [] := by
      simp [foundNewRunTraced?, hempty, TraceResult.pure,
        AccessTrace.empty]
    refine ⟨result, ?_⟩
    exact
      { resultEq := hresult
        returnCode := rfl
        resultFuel := rfl
        traceFuel := by
          simpa only [foundNewRunTraced?, if_pos hempty] using hpure.fuel
        accessesInBounds := by
          simpa only [foundNewRunTraced?, if_pos hempty] using hpure.bounds
        tempAccessesLive := by
          simpa only [foundNewRunTraced?, if_pos hempty] using hpure.tempLive
        noPushes := by
          simpa only [foundNewRunTraced?, if_pos hempty] using hpure.noPushes
        exactErasure := hexact
        tempInvariant := hInv
        tempLive := hLive
        valuesMode := hMode
        hasValuesFrame := rfl
        stableFrame := FoundNewRunStableFrame.refl state
        memoryEventsValid := by
          simp [AccessTrace.memoryEventsValid, hmemoryEvents]
        onlyMergeMemoryEvents := by
          simp [AccessTrace.onlyMergeMemoryEvents, hmemoryEvents]
        memoryEventsBounded := by
          intro _
          simp [AccessTrace.mergeMemoryEventsBounded, hmemoryEvents]
        physicalSlotsBound := by
          intro hbound
          exact hbound
        memorySegment := by
          refine ⟨[], hmemoryEvents, ?_⟩
          rw [AccessTrace.MergeMemoryCallChain.nil_iff]
          simp [result, foundNewRunSuccessResult]
        readyToPush := hready }
  · have hnonempty : state.pending.toList ≠ [] := by
    intro hpending
    apply hempty
    rw [Array.isEmpty_iff_size_eq_zero]
    have hlength := congrArg List.length hpending
    simpa using hlength
    obtain hpending | := List.eq_nil_or_concat' state.pending.toList
      ⟨before, top, hsplit⟩
    · exact (hnonempty hpending).elim
    · have hsize : state.pending.size = before.length + 1 := by
      have hlength := congrArg List.length hsplit
      simpa using hlength
      have htopIndex : state.pending.size - 1 < state.pending.size := by
        omega
      have htopLookup :
        state.pending[state.pending.size - 1]? = some top := by
        rw [← Array.getElem?_toList, hsplit, hsize]
        simp
      have htopRead :
        (TraceResult.pendingRunRead? state
          (Int.ofNat (state.pending.size - 1))).result = some top := by
        have hget : state.pending[state.pending.size - 1] = top := by
          rw [Array.getElem?_eq_getElem htopIndex] at htopLookup
          exact Option.some.inj htopLookup
        rw [pendingRunRead_result_of_bounds state
          (state.pending.size - 1) htopIndex, hget]
      have htopReadSafe : MovementTraceSafe
        (TraceResult.pendingRunRead? state
          (Int.ofNat (state.pending.size - 1))) :=
        pendingRunRead_safe state _
          ⟨Int.natCast_nonneg _, by simpa using htopIndex⟩
      have hcover : PendingRunsCover state.basekeys
        (state.basekeys + scanned) (before ++ [top]) := by
        simpa [hsplit] using hlayout.2.2.2
      have htopSpec := hcover.member_spec (run := top) (by simp)
      have htopEnd : top.endIndex = state.basekeys + scanned :=
        PendingRunsCover.last_end_eq hcover
      have hfits : top.base - state.basekeys + top.len.toNat +
        newRun.len.toNat ≤ state.listlen.toNat := by
        simp only [PendingRun.endIndex] at htopEnd
        omega
      have hnewMax : newRun.len.toNat ≤ PY_SSIZE_T_MAX := by
        have : newRun.len.toNat ≤ PY_LIST_MAX := by omega
        norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at this ⊢
        omega
      have htopSlt : (0 : PySSize).slt top.len :=
        pySSize_slt_zero_of_nonnegative_positive top.len
          htopSpec.2.1 htopSpec.2.2.1
      have hguard :
        ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
          (0 : PySSize).slt top.len && decide (0 < newRun.len.toNat) &&
          decide (newRun.len.toNat ≤ PY_SSIZE_T_MAX) &&
          decide (top.base - state.basekeys + top.len.toNat +
            newRun.len.toNat ≤ state.listlen.toNat)) = true := by
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        exact ⟨⟨⟨⟨⟨hlayout.1, htopSpec.1⟩, htopSlt⟩,
          hnewPositive⟩, hnewMax⟩, hfits⟩
      have hvalidNat := validPowerloopInput_ofNat
        (s := top.base - state.basekeys) (u := top.len.toNat)
        (v := newRun.len.toNat) (n := state.listlen.toNat)
        htopSpec.2.2.1 hnewPositive hfits hmax
      have htopLen : BitVec.ofNat 64 top.len.toNat = top.len := by simp
      have hnewLen : BitVec.ofNat 64 newRun.len.toNat = newRun.len := by simp
      have hlistlen :
        BitVec.ofNat 64 state.listlen.toNat = state.listlen := by simp
      have hvalid : ValidPowerloopInput
        (BitVec.ofNat 64 (top.base - state.basekeys)) top.len newRun.len
        state.listlen := by
        simpa [htopLen, hnewLen, hlistlen] using hvalidNat
      let powered := powerloopTraced
        (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
        (BitVec.ofNat 64 newRun.len.toNat) state.listlen
      have hstopped : powered.stopped = true := by
        simpa [powered, hnewLen] using
          (powerloopTraceSafety
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            newRun.len state.listlen hvalid).2
      have hpower : powered.result = pendingBoundaryPower state.basekeys
        state.listlen top newRun := by
        dsimp [powered, pendingBoundaryPower, powerloop]
        rw [hnewLen]
      rcases foundNewRunLoopTraced_safe state.pending.size state scanned
        before top newRun powered.result rfl hmax hlayout hpowered hsplit
        hnewBase hnewNonnegative hnewPositive hnewWithin hpower hInv hLive
        hMode with ⟨result, hloop⟩
      have hresult :
        (foundNewRunTraced? state newRun.len.toNat).result = some result := by
        unfold foundNewRunTraced?
        rw [if_neg hempty]
        rw [TraceResult.bind_result_of_eq_some _ _ top htopRead]
        rw [if_pos hguard]
        simp only [powered, hstopped, Bool.not_true, Bool.false_eq_true,
          if_false]
        exact hloop.resultEq
      have htraceSafe :
        MovementTraceSafe (foundNewRunTraced? state newRun.len.toNat) := by
        unfold foundNewRunTraced?
        rw [if_neg hempty]
        apply MovementTraceSafe.bind _ _ top htopRead htopReadSafe
        rw [if_pos hguard]
        simp only [powered, hstopped, Bool.not_true, Bool.false_eq_true,
          if_false]
        exact hloop.traceSafe
      have hmemoryEvents :
        (foundNewRunTraced? state newRun.len.toNat).trace.memoryEvents =
          (foundNewRunLoopTraced? state.pending.size state
            powered.result).trace.memoryEvents := by
        unfold foundNewRunTraced?
        rw [if_neg hempty]
        simp only [TraceResult.trace_bind, htopRead]
        rw [if_pos hguard]
        simp only [powered, hstopped, Bool.not_true, Bool.false_eq_true,
          if_false, AccessTrace.memoryEvents_compose,
          TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess,
          List.nil_append]
      have hexact :
        (foundNewRunTraced? state newRun.len.toNat).erase =
          foundNewRun? state newRun.len.toNat := by
        unfold foundNewRunTraced? foundNewRun?
        simp only [if_neg hempty, TraceResult.erase_bind,
          TraceResult.erase_pendingRunRead]
        have hnonnegative :
          0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
        rw [if_pos hnonnegative]
        have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
          state.pending.size - 1 := rfl
        rw [htoi, htopLookup]
        simp only [Option.bind_some, if_pos hguard, powered, hstopped,
          Bool.not_true, Bool.false_eq_true, if_false]
        exact hloop.exactErasure
      have hraw : foundNewRun? state newRun.len.toNat = some result := by
        rwa [← hexact]
      have houtside : newRun ∉ state.pending.toList :=
        newRun_not_mem_of_layout hlayout hnewBase
      have hready := foundNewRun_preserves_readyToPush state scanned newRun
        result hmax hlayout hpowered hnewBase hnewNonnegative hnewPositive
        hnewWithin houtside hraw hloop.returnCode hloop.resultFuel
      refine ⟨result, ?_⟩
      exact
        { resultEq := hresult
          returnCode := hloop.returnCode
          resultFuel := hloop.resultFuel
          traceFuel := htraceSafe.fuel
          accessesInBounds := htraceSafe.bounds
          tempAccessesLive := htraceSafe.tempLive
          noPushes := htraceSafe.noPushes
          exactErasure := hexact
          tempInvariant := hloop.tempInvariant
          tempLive := hloop.tempLive
          valuesMode := hloop.valuesMode
          hasValuesFrame := hloop.hasValuesFrame
          stableFrame := hloop.stableFrame
          memoryEventsValid := by
            rw [AccessTrace.memoryEventsValid]
            intro event hevent
            rw [hmemoryEvents] at hevent
            exact hloop.memoryEventsValid event hevent
          onlyMergeMemoryEvents := by
            rw [AccessTrace.onlyMergeMemoryEvents]
            intro event hevent
            rw [hmemoryEvents] at hevent
            exact hloop.onlyMergeMemoryEvents event hevent
          memoryEventsBounded := by
            intro hbound
            rw [AccessTrace.mergeMemoryEventsBounded]
            intro event hevent
            rw [hmemoryEvents] at hevent
            exact hloop.memoryEventsBounded hbound event hevent
          physicalSlotsBound := hloop.physicalSlotsBound
          memorySegment := by
            obtain ⟨calls, hevents, hchain⟩ := hloop.memorySegment
            exact ⟨calls, hmemoryEvents.trans hevents, hchain⟩
          readyToPush := hready }

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRun_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRun_safe
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hnewBase : newRun.base = state.basekeys + scanned)
  (hnewNonnegative : newRun.len.Nonnegative)
  (hnewPositive : 0 < newRun.len.toNat)
  (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
-- imply
  ∃ result, FoundNewRunSafetyPost state scanned newRun result :=
-- proof
  foundNewRun_safe_core state scanned newRun hmax hlayout hpowered hnewBase
    hnewNonnegative hnewPositive hnewWithin hInv hLive hMode

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunLoopTraced_zero_traceFuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunLoopTraced_zero_traceFuel
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {power : Nat} :
-- imply
  (foundNewRunLoopTraced? 0 state power).trace.fuelExhausted = true := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_foundNewRunLoopTraced_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma erase_foundNewRunLoopTraced_zero
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {power : Nat} :
-- imply
  (foundNewRunLoopTraced? 0 state power).erase = foundNewRunLoop? 0 state power := by
-- proof
  simp [foundNewRunLoopTraced?, foundNewRunLoop?,
    foundNewRunOutOfFuelResult]

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunLoopTraced_zero_result](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunLoopTraced_zero_result
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {power : Nat} :
-- imply
  (foundNewRunLoopTraced? 0 state power).result.map (fun result => (result.returnCode, result.fuelExhausted)) = some (-1, true) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunTraced_empty_accesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunTraced_empty_accesses
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {n2 : Nat}
-- given
  (hempty : state.pending.isEmpty = true) :
-- imply
  (foundNewRunTraced? state n2).trace.accesses = [] := by
-- proof
  unfold foundNewRunTraced?
  rw [if_pos hempty]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunTraced_top_read_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunTraced_top_read_prefix
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {n2 : Nat}
-- given
  (hsize : 0 < state.pending.size) :
-- imply
  ∃ tail, (foundNewRunTraced? state n2).trace.accesses = { kind := .read region := .pendingRuns index := Int.ofNat (state.pending.size - 1) extent := state.pending.size } :: tail := by
-- proof
  have hnotEmpty : state.pending.isEmpty ≠ true := by
    intro hempty
    rw [Array.isEmpty_iff_size_eq_zero] at hempty
    omega
  have hindex : state.pending.size - 1 < state.pending.size := by omega
  let top := state.pending[state.pending.size - 1]
  have hread :
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).result = some top := by
    exact pendingRunRead_result_of_bounds state _ hindex
  unfold foundNewRunTraced?
  rw [if_neg hnotEmpty, TraceResult.trace_bind, hread]
  simp only [TraceResult.trace_pendingRunRead, AccessTrace.compose,
    AccessTrace.singletonAccess, List.singleton_append, List.cons.injEq,
    true_and]
  exact ⟨_, rfl⟩

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunTraced_loop_entry_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunTraced_loop_entry_trace
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {n2 : Nat}
  {top : PendingRun}
-- given
  (hnonempty : state.pending.isEmpty ≠ true)
  (htop : state.pending[state.pending.size - 1]? = some top)
  (hguard : ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) && (0 : PySSize).slt top.len && decide (0 < n2) && decide (n2 ≤ PY_SSIZE_T_MAX) && decide (top.base - state.basekeys + top.len.toNat + n2 ≤ state.listlen.toNat)) = true)
  (hstopped : (powerloopTraced (BitVec.ofNat 64 (top.base - state.basekeys)) top.len (BitVec.ofNat 64 n2) state.listlen).stopped = true) :
-- imply
  (foundNewRunTraced? state n2).trace = (TraceResult.pendingRunRead? state (Int.ofNat (state.pending.size - 1))).trace.compose (foundNewRunLoopTraced? state.pending.size state (powerloopTraced (BitVec.ofNat 64 (top.base - state.basekeys)) top.len (BitVec.ofNat 64 n2) state.listlen).result).trace := by
-- proof
  have hread :
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).result = some top := by
    change (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).erase = some top
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative :
      0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
      state.pending.size - 1 := rfl
    rw [htoi, htop]
  unfold foundNewRunTraced?
  rw [if_neg hnonempty, TraceResult.trace_bind, hread]
  simp only
  rw [if_pos hguard]
  simp only [hstopped, Bool.not_true, Bool.false_eq_true, if_false]

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunLoopTraced_secondLast_read_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunLoopTraced_secondLast_read_prefix
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {state : MergeState κ ν}
  {power : Nat}
-- given
  (hmany : 1 < state.pending.size) :
-- imply
  ∃ tail, (foundNewRunLoopTraced? (fuel + 1) state power).trace.accesses = { kind := .read region := .pendingRuns index := Int.ofNat (state.pending.size - 2) extent := state.pending.size } :: tail := by
-- proof
  have hindex : state.pending.size - 2 < state.pending.size := by omega
  let preceding := state.pending[state.pending.size - 2]
  have hread :
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 2))).result = some preceding := by
    exact pendingRunRead_result_of_bounds state _ hindex
  simp only [foundNewRunLoopTraced?, hmany, if_pos,
    TraceResult.trace_bind, hread, TraceResult.trace_pendingRunRead,
    AccessTrace.compose, AccessTrace.singletonAccess, List.singleton_append]
  exact ⟨_, rfl⟩

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunLoopTraced_merge_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunLoopTraced_merge_trace_order
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {state : MergeState κ ν}
  {power : Nat}
  {preceding : PendingRun}
  {precedingPower : Nat}
  {merged : MergeAtResult κ ν}
-- given
  (hmany : 1 < state.pending.size)
  (hlookup : state.pending[state.pending.size - 2]? = some preceding)
  (hprecedingPower : preceding.power = some precedingPower)
  (hguard : power < precedingPower)
  (hmerge : (mergeAtTraced? state (state.pending.size - 2)).result = some merged)
  (hsuccess : merged.returnCode = 0 ∧ !merged.fuelExhausted) :
-- imply
  (foundNewRunLoopTraced? (fuel + 1) state power).trace = (AccessTrace.singletonAccess .read .pendingRuns (Int.ofNat (state.pending.size - 2)) state.pending.size).compose ((mergeAtTraced? state (state.pending.size - 2)).trace.compose (foundNewRunLoopTraced? fuel merged.state power).trace) := by
-- proof
  have hindex : state.pending.size - 2 < state.pending.size := by omega
  have hread :
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 2))).result = some preceding := by
    have hget : state.pending[state.pending.size - 2] = preceding := by
      rw [Array.getElem?_eq_getElem hindex] at hlookup
      exact Option.some.inj hlookup
    rw [pendingRunRead_result_of_bounds state
      (state.pending.size - 2) hindex, hget]
  simp only [foundNewRunLoopTraced?, hmany, if_pos,
    TraceResult.trace_bind, hread]
  rw [hprecedingPower]
  simp only
  rw [if_pos hguard, TraceResult.trace_bind, hmerge]
  simp only
  rw [if_pos hsuccess, TraceResult.trace_pendingRunRead]

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunLoop_fuel_tracks_top_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunLoop_fuel_tracks_top_merge
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {before : List PendingRun}
  {state after : MergeState κ ν}
  {left right merged : PendingRun}
-- given
  (hfuel : fuel + 1 = state.pending.size)
  (hbefore : state.pending.toList = before ++ [left, right])
  (hafter : after.pending.toList = before ++ [merged]) :
-- imply
  fuel = after.pending.size := by
-- proof
  have hbeforeLength := congrArg List.length hbefore
  have hafterLength := congrArg List.length hafter
  simp only [Array.length_toList, List.length_append, List.length_cons,
    List.length_nil] at hbeforeLength hafterLength
  omega

end CPythonListsort

namespace CPythonListsort

/--
[setTopPowerTraced_singleton_write](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma setTopPowerTraced_singleton_write
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {power : Nat}
-- given
  (hsize : 0 < state.pending.size) :
-- imply
  (setTopPowerTraced? state power).trace.accesses = [{ kind := .write region := .pendingRuns index := Int.ofNat (state.pending.size - 1) extent := state.pending.size }] := by
-- proof
  have hnotEmpty : state.pending.isEmpty ≠ true := by
    intro hempty
    rw [Array.isEmpty_iff_size_eq_zero] at hempty
    omega
  unfold setTopPowerTraced?
  rw [if_neg hnotEmpty]
  simp [TraceResult.trace_pendingRunPowerWrite,
    AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunLoopTraced_singleton_write](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunLoopTraced_singleton_write
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {state : MergeState κ ν}
  {power : Nat}
-- given
  (hsize : state.pending.size = 1) :
-- imply
  (foundNewRunLoopTraced? (fuel + 1) state power).trace.accesses = [{ kind := .write region := .pendingRuns index := 0 extent := 1 }] := by
-- proof
  have hnotMany : ¬1 < state.pending.size := by omega
  simp only [foundNewRunLoopTraced?, hnotMany, if_false]
  change (setTopPowerTraced? state power).trace.accesses = _
  rw [setTopPowerTraced_singleton_write state power (by omega)]
  simp [hsize]

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunTraced_powerloop_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunTraced_powerloop_exhaustion
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {n2 : Nat}
  {top : PendingRun}
-- given
  (hnonempty : state.pending.isEmpty ≠ true)
  (htop : state.pending[state.pending.size - 1]? = some top)
  (hguard : ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) && (0 : PySSize).slt top.len && decide (0 < n2) && decide (n2 ≤ PY_SSIZE_T_MAX) && decide (top.base - state.basekeys + top.len.toNat + n2 ≤ state.listlen.toNat)) = true)
  (hstopped : (powerloopTraced (BitVec.ofNat 64 (top.base - state.basekeys)) top.len (BitVec.ofNat 64 n2) state.listlen).stopped = false) :
-- imply
  (foundNewRunTraced? state n2).trace.fuelExhausted = true ∧ (foundNewRunTraced? state n2).erase = foundNewRun? state n2 := by
-- proof
  have hread :
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).result = some top := by
    change (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).erase = some top
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative :
      0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
      state.pending.size - 1 := rfl
    rw [htoi, htop]
  constructor
  · unfold foundNewRunTraced?
    rw [if_neg hnonempty, TraceResult.trace_bind, hread]
    simp only
    rw [if_pos hguard]
    simp [hstopped, TraceResult.markFuelExhausted, AccessTrace.compose,
      AccessTrace.exhausted]
  · unfold foundNewRunTraced? foundNewRun?
    simp only [if_neg hnonempty, TraceResult.erase_bind,
      TraceResult.erase_pendingRunRead]
    have hnonnegative :
      0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
      state.pending.size - 1 := rfl
    rw [htoi, htop]
    simp only [Option.bind_some, if_pos hguard, hstopped, Bool.not_false,
      if_pos, TraceResult.erase_markFuelExhausted, TraceResult.erase_pure]
    simp [foundNewRunOutOfFuelResult]

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunTraced_singleton_access_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunTraced_singleton_access_order
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {n2 : Nat}
  {top : PendingRun}
-- given
  (hsize : state.pending.size = 1)
  (htop : state.pending[0]? = some top)
  (hguard : ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) && (0 : PySSize).slt top.len && decide (0 < n2) && decide (n2 ≤ PY_SSIZE_T_MAX) && decide (top.base - state.basekeys + top.len.toNat + n2 ≤ state.listlen.toNat)) = true)
  (hstopped : (powerloopTraced (BitVec.ofNat 64 (top.base - state.basekeys)) top.len (BitVec.ofNat 64 n2) state.listlen).stopped = true) :
-- imply
  (foundNewRunTraced? state n2).trace.accesses = [{ kind := .read, region := .pendingRuns, index := 0, extent := 1 }, { kind := .write, region := .pendingRuns, index := 0, extent := 1 }] := by
-- proof
  have hnotEmpty : state.pending.isEmpty ≠ true := by
    intro hempty
    rw [Array.isEmpty_iff_size_eq_zero] at hempty
    omega
  have htop' : state.pending[state.pending.size - 1]? = some top := by
    simpa [hsize] using htop
  have hread :
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).result = some top := by
    change (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).erase = some top
    rw [TraceResult.erase_pendingRunRead]
    have hnonnegative :
      0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [if_pos hnonnegative]
    have htoi : (Int.ofNat (state.pending.size - 1)).toNat =
      state.pending.size - 1 := rfl
    rw [htoi, htop']
  have hloop := foundNewRunLoopTraced_singleton_write 0 state
    (powerloopTraced (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
      (BitVec.ofNat 64 n2) state.listlen).result hsize
  unfold foundNewRunTraced?
  rw [if_neg hnotEmpty, TraceResult.trace_bind, hread]
  simp only
  rw [if_pos hguard]
  simp only [hstopped, Bool.not_true, Bool.false_eq_true, if_false]
  rw [show state.pending.size = 0 + 1 by omega]
  change
    (TraceResult.pendingRunRead? state (Int.ofNat 0)).trace.accesses ++
      (foundNewRunLoopTraced? (0 + 1) state
        (powerloopTraced
          (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
          (BitVec.ofNat 64 n2) state.listlen).result).trace.accesses = _
  rw [hloop]
  simp [TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess, hsize]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[foundNewRunUnpoweredRegressionState_not_powered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
private lemma foundNewRunUnpoweredRegressionState_not_powered :
  ¬PoweredPrefix foundNewRunUnpoweredRegressionState := by
  intro hpowered
  obtain hempty | := hpowered
    ⟨olderRuns, top, hsplit, hpowers, _hexact⟩
  · simp [foundNewRunUnpoweredRegressionState] at hempty
  · have hsplit' :
    [foundNewRunUnpoweredOlder, foundNewRunUnpoweredNewest] =
      olderRuns ++ [top] := by
    simpa [foundNewRunUnpoweredRegressionState] using hsplit
    have holderRunsLength : olderRuns.length = 1 := by
      have := congrArg List.length hsplit'
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      omega
    obtain ⟨only, rfl⟩ := List.length_eq_one_iff.mp holderRunsLength
    simp only [List.singleton_append, List.cons.injEq] at hsplit'
    have honly := hpowers.run_power (run := only) (by simp)
    obtain ⟨storedPower, hsome, _hrange⟩ := honly
    have hsomeOlder : foundNewRunUnpoweredOlder.power = some storedPower := by
      simpa [hsplit'.1] using hsome
    simp [foundNewRunUnpoweredOlder] at hsomeOlder

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunLoopTraced_unpowered_preceding_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunLoopTraced_unpowered_preceding_failure
  {κ : Type u}
  {ν : Type v} :
-- imply
  ¬PoweredPrefix foundNewRunUnpoweredRegressionState ∧ (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).result = none ∧ (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).trace.accesses = [{ kind := .read region := .pendingRuns index := 0 extent := 2 }] ∧ (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).trace.fuelExhausted = false ∧ (foundNewRunLoopTraced? 2 foundNewRunUnpoweredRegressionState 1).trace.pushDepths = [] := by
-- proof
  refine ⟨foundNewRunUnpoweredRegressionState_not_powered, ?_⟩
  decide

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRunTraced_unpowered_prefix_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean)
-/
@[path]
lemma foundNewRunTraced_unpowered_prefix_failure
  {κ : Type u}
  {ν : Type v} :
-- imply
  ¬PoweredPrefix foundNewRunUnpoweredRegressionState ∧ (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).result = none ∧ (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).trace.accesses = [{ kind := .read region := .pendingRuns index := 1 extent := 2 }, { kind := .read region := .pendingRuns index := 0 extent := 2 }] ∧ (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).trace.fuelExhausted = false ∧ (foundNewRunTraced? foundNewRunUnpoweredRegressionState 1).trace.pushDepths = [] := by
-- proof
  refine ⟨foundNewRunUnpoweredRegressionState_not_powered, ?_⟩
  decide

end CPythonListsort


-- created on 2026-10-23
