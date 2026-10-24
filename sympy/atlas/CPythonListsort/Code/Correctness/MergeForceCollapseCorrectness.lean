/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeForceCollapseSafety
import sympy.atlas.CPythonListsort.Code.Correctness.MergeAtCorrectness

/-!
# Functional correctness of `merge_force_collapse`

The final collapse repeatedly delegates to the already-correct `merge_at`
implementation.  This module carries the pending-run correctness and complete
entry snapshot through the actual fuel-bounded collapse evaluator; it does not
replace that evaluator by a mathematical fold.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- End-to-end correctness at the final-collapse boundary.  Safety is embedded
verbatim so the semantic result is tied to the real composed trace. -/
structure MergeForceCollapseCorrectnessPost
    (lt : BoolComparator alpha) (input : Array alpha)
    (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) : Prop where
  safety : MergeForceCollapseSafetyPost pre scanned result
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

private structure MergeForceCollapseLoopCorrectnessPost
    (lt : BoolComparator alpha) (input : Array alpha)
    (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned fuel : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) : Prop where
  resultEq :
    (mergeForceCollapseLoopTraced? fuel pre).result = some result
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

private def forceCollapseCorrectnessRegressionLt : BoolComparator Nat :=
  fun _ _ => false

private def forceCollapseCorrectnessRegressionEntry
    (origin payload : Nat) : SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 7, origin := origin }, value := some payload }

private def forceCollapseCorrectnessRegressionState :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[forceCollapseCorrectnessRegressionEntry 0 10,
            forceCollapseCorrectnessRegressionEntry 1 20,
            forceCollapseCorrectnessRegressionEntry 2 30] }
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 1 },
        { base := 1, len := 1, power := some 2 },
        { base := 2, len := 1, power := none }]
    key_compare := occurrenceComparator forceCollapseCorrectnessRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private structure ForceCollapseCorrectnessRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  pending : List (Nat × Nat)
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

private def forceCollapseCorrectnessRegressionView
    (result : MergeForceCollapseResult (Occurrence Nat) Nat) :
    ForceCollapseCorrectnessRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    pending := result.state.pending.toList.map (fun run =>
      (run.base, run.len.toNat))
    entries := result.state.data.entries.toList.map (fun entry =>
      (entry.key.value, entry.key.origin, entry.value)) }

private def forceCollapseCorrectnessRegressionExpected :
    ForceCollapseCorrectnessRegressionView :=
  { returnCode := 0
    fuelExhausted := false
    pending := [(0, 3)]
    entries := [(7, 0, some 10), (7, 1, some 20), (7, 2, some 30)] }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Native evaluation unfolds two complete merge continuations and their loops.
set_option linter.style.nativeDecide false in
