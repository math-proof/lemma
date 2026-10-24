import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness
open CPythonListsort CPythonListsort.MergeForceCollapseCorrectnessPost


namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[traceResult_bind_result_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean)
-/
@[path]
private lemma traceResult_bind_result_of_eq_some
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

variable {alpha : Type u} {nu : Type v}
/--
[mergeForceCollapseLoop_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean)
-/
@[path]
step obtains its next state from `mergeAt_correct`; no independent abstract
merge transition is assumed. -/
private lemma mergeForceCollapseLoop_correct
  {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
  (input : Array alpha) (source : SortSlice alpha nu)
  (fuel : Nat) (state : MergeState (Occurrence alpha) nu) (scanned : Nat)
  (hfuel : fuel = state.pending.size)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hnonempty : state.pending.toList ≠ [])
  (hcorrect : PendingRunsCorrect lt input state scanned)
  (hsnapshot : EntrySnapshotPermutation source state.data)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hcompare : state.key_compare = occurrenceComparator lt) :
  ∃ result,
    MergeForceCollapseLoopCorrectnessPost lt input source state scanned fuel
      result := by
  induction fuel generalizing state with
  | zero =>
    have hpositive : 0 < state.pending.size := by
      have := List.length_pos_of_ne_nil hnonempty
      simpa using this
    omega
  | succ remaining ih =>
    by_cases hmany : 1 < state.pending.size
    · rcases forceCollapseIndexTraced_safe state hmany with
      ⟨i, hindexResult, _hindexSafe, _hindexErasure, hposition⟩
      rcases mergeAt_correct horder input source state scanned i hcorrect
        hsnapshot hcompare hmax hposition hInv hLive hMode with
        ⟨merged, hmerged⟩
      obtain ⟨left, right, hselected⟩ := hmerged.selected
      rcases hselected.pendingSplice with
        ⟨before, after, _hbeforeLength, hbeforePending, hafterPending⟩
      have hremaining : remaining = merged.state.pending.size :=
        mergeForceCollapseLoop_fuel_tracks_merge remaining state merged.state
          before after left right
          ({ left with len := left.len + right.len } : PendingRun)
          (by simpa [Nat.succ_eq_add_one] using hfuel)
          hbeforePending hafterPending
      have hmergedNonempty : merged.state.pending.toList ≠ [] := by
        rw [hafterPending]
        simp
      have hmergedMax : merged.state.listlen.toNat ≤ PY_LIST_MAX := by
        rwa [hmerged.safety.stableFrame.listlen]
      rcases ih merged.state hremaining hmergedMax hmergedNonempty
        hmerged.pendingRunsCorrect hmerged.entrySnapshot
        hmerged.safety.tempInvariant hmerged.safety.tempLive
        hmerged.safety.valuesMode hmerged.comparator with
        ⟨result, hrest⟩
      have hmergeSuccess :
        merged.returnCode = 0 ∧ !merged.fuelExhausted :=
        ⟨hmerged.safety.returnCode,
          by simp [hmerged.safety.resultFuel]⟩
      have hresult :
        (mergeForceCollapseLoopTraced? (remaining + 1) state).result =
          some result := by
        simp only [mergeForceCollapseLoopTraced?, hmany, if_true]
        rw [traceResult_bind_result_of_eq_some _ _ i hindexResult]
        rw [traceResult_bind_result_of_eq_some _ _ merged
          hmerged.safety.resultEq]
        rwa [if_pos hmergeSuccess]
      have hrestFrame : SortSlice.EqualOutsideRange merged.state.data
        result.state.data state.basekeys scanned := by
        simpa [hmerged.safety.stableFrame.basekeys] using hrest.consumedFrame
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
          simpa [Nat.succ_eq_add_one] using hresult
          pendingRunsCorrect := hrest.pendingRunsCorrect
          entrySnapshot := hrest.entrySnapshot
          comparator := hrest.comparator
          consumedFrame := hmerged.consumedFrame.trans hrestFrame }
    · have hsizeOne : state.pending.size = 1 := by
      have hpositive : 0 < state.pending.size := by
        have := List.length_pos_of_ne_nil hnonempty
        simpa using this
      omega
      let result : MergeForceCollapseResult (Occurrence alpha) nu :=
        { state := state, returnCode := 0, fuelExhausted := false }
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
          simp only [mergeForceCollapseLoopTraced?, hmany, if_false]
          rfl
          pendingRunsCorrect := by simpa [result] using hcorrect
          entrySnapshot := by simpa [result] using hsnapshot
          comparator := by simpa [result] using hcompare
          consumedFrame := by
            simpa [result] using
              (SortSlice.EqualOutsideRange.refl state.data state.basekeys
                scanned) }

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapse_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean)
-/
@[path]
lemma mergeForceCollapse_correct
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : Array alpha}
  {source : SortSlice alpha nu}
  {state : MergeState (Occurrence alpha) nu}
  {scanned : Nat}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hnonempty : state.pending.toList ≠ [])
  (hcorrect : PendingRunsCorrect lt input state scanned)
  (hsnapshot : EntrySnapshotPermutation source state.data)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  ∃ result, MergeForceCollapseCorrectnessPost lt input source state scanned result := by
-- proof
  rcases mergeForceCollapseLoop_correct horder input source state.pending.size
    state scanned rfl hmax hnonempty hcorrect hsnapshot hInv hLive hMode
    hcompare with ⟨semanticResult, hsemantic⟩
  rcases mergeForceCollapse_safe state scanned hmax hnonempty hcorrect.layout
    hInv hLive hMode with ⟨safeResult, hsafety⟩
  have hsafetyLoop :
    (mergeForceCollapseLoopTraced? state.pending.size state).result =
      some safeResult := by
    simpa [mergeForceCollapseTraced?] using hsafety.resultEq
  have hresults : safeResult = semanticResult := by
    exact Option.some.inj (hsafetyLoop.symm.trans hsemantic.resultEq)
  subst semanticResult
  exact
    ⟨safeResult,
      { safety := hsafety
        pendingRunsCorrect := hsemantic.pendingRunsCorrect
        entrySnapshot := hsemantic.entrySnapshot
        comparator := hsemantic.comparator
        consumedFrame := hsemantic.consumedFrame }⟩

end CPythonListsort

namespace CPythonListsort.MergeForceCollapseCorrectnessPost

/--
[finalRunCorrect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean)
-/
@[path]
lemma finalRunCorrect
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : Array alpha}
  {source : SortSlice alpha nu}
  {pre : MergeState (Occurrence alpha) nu}
  {scanned : Nat}
  {result : MergeForceCollapseResult (Occurrence alpha) nu}
-- given
  (h : MergeForceCollapseCorrectnessPost lt input source pre scanned result) :
-- imply
  ∃ run, result.state.pending.toList = [run] ∧ run.base = pre.basekeys ∧ run.endIndex = pre.basekeys + scanned ∧ Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys result.state run) ∧ StableOccurrencePermutation lt (canonicalOccurrenceSegment input pre.basekeys scanned) (pendingRunOccurrenceKeys result.state run).toList := by
-- proof
  obtain ⟨run, hpending, hbase, hend⟩ := h.safety.finalRun
  have hmember : run ∈ result.state.pending.toList := by
    rw [hpending]
    simp
  have hsorted := h.pendingRunsCorrect.runSorted run hmember
  have hstable := h.pendingRunsCorrect.stableOccurrencePermutation
  refine ⟨run, hpending, hbase, hend, hsorted, ?_⟩
  simpa [pendingOccurrenceKeys, hpending,
    h.safety.stableFrame.basekeys] using hstable

end CPythonListsort.MergeForceCollapseCorrectnessPost

namespace CPythonListsort

/--
[mergeForceCollapseTraced_singleton_noop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean)
-/
@[path]
lemma mergeForceCollapseTraced_singleton_noop
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState κ ν}
  {run : PendingRun}
-- given
  (hpending : state.pending.toList = [run]) :
-- imply
  (mergeForceCollapseTraced? state).result = some { state := state, returnCode := 0, fuelExhausted := false } := by
-- proof
  have hsize : state.pending.size = 1 := by
    have := congrArg List.length hpending
    simpa using this
  simp only [mergeForceCollapseTraced?, hsize,
    mergeForceCollapseLoopTraced?]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapse_threeRun_equalKey_payload_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean)
-/
@[path]
lemma mergeForceCollapse_threeRun_equalKey_payload_regression
  {alpha : Type u}
  {nu : Type v} :
-- imply
  (mergeForceCollapse? forceCollapseCorrectnessRegressionState).map forceCollapseCorrectnessRegressionView = some forceCollapseCorrectnessRegressionExpected := by
-- proof
  native_decide

end CPythonListsort


-- created on 2026-10-23
