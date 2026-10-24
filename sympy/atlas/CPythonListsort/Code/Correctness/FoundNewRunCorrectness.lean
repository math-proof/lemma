/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/FoundNewRunCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.FoundNewRunSafety
import sympy.atlas.CPythonListsort.Code.Correctness.MergeAtCorrectness

/-!
# Functional correctness of `found_new_run`

This module carries pending-run correctness and the persistent whole-entry
snapshot through the actual `foundNewRunLoop?` collapse loop.  Pending-power
writes are proved semantically inert, while every taken merge is discharged by
`mergeAt_correct`.
-/

namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

/-- Semantic state facts preserved by the collapse loop.  The frame is stated
relative to the loop call state, so recursive merge frames compose directly. -/
private structure FoundNewRunSemanticPost
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν)
    (pre : MergeState (Occurrence α) ν) (scanned : Nat)
    (result : FoundNewRunResult (Occurrence α) ν) : Prop where
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

/-- End-to-end functional certificate for one admitted `found_new_run` call. -/
structure FoundNewRunCorrectnessPost
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν)
    (pre : MergeState (Occurrence α) ν) (scanned : Nat)
    (newRun : PendingRun)
    (result : FoundNewRunResult (Occurrence α) ν) : Prop where
  safety : FoundNewRunSafetyPost pre scanned newRun result
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

/-- The precise portion of `mergeAt_correct` consumed by the loop induction.
Keeping it as a parameter lets the recursion expose that every taken merge,
and only a taken merge, invokes the full correctness theorem. -/
private def MergeAtCorrectnessProvider
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν)
    (scanned : Nat) : Prop :=
  ∀ (pre : MergeState (Occurrence α) ν) (i : Nat),
    PendingRunsCorrect lt input pre scanned →
    EntrySnapshotPermutation source pre.data →
    pre.key_compare = occurrenceComparator lt →
    pre.listlen.toNat ≤ PY_LIST_MAX →
    (i + 2 = pre.pending.size ∨ i + 3 = pre.pending.size) →
    TempStorageInv pre.a pre.alloced →
    pre.a.Live →
    SortSlice.ValuesModeInvariant pre.a.hasValues pre.data →
    ∃ merged,
      MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) merged ∧
        PendingRunsCorrect lt input merged.state scanned ∧
        EntrySnapshotPermutation source merged.state.data ∧
        merged.state.key_compare = occurrenceComparator lt ∧
        SortSlice.EqualOutsideRange pre.data merged.state.data
          pre.basekeys scanned

private def foundNewRunTakenMergeLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def foundNewRunTakenMergeEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

private def foundNewRunTakenMergeState : MergeState (Occurrence Nat) PUnit :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[foundNewRunTakenMergeEntry 2 0,
            foundNewRunTakenMergeEntry 1 1,
            foundNewRunTakenMergeEntry 3 2] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 3 },
        { base := 1, len := 1, power := none }]
    key_compare := occurrenceComparator foundNewRunTakenMergeLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option linter.style.nativeDecide false in
