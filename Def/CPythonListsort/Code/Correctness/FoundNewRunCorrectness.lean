/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/FoundNewRunCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.FoundNewRunSafety.Part2
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectness.Part2
import Structure.CPythonListsort.Code.Correctness.FoundNewRunCorrectness
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

/-- The precise portion of `mergeAt_correct` consumed by the loop induction.
Keeping it as a parameter lets the recursion expose that every taken merge,
and only a taken merge, invokes the full correctness theorem. -/
def MergeAtCorrectnessProvider
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

def foundNewRunTakenMergeLt : BoolComparator Nat :=
  fun left right => decide (left < right)

def foundNewRunTakenMergeEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

def foundNewRunTakenMergeState : MergeState (Occurrence Nat) PUnit :=
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

end CPythonListsort
