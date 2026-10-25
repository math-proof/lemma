/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.Order.Part4
import Def.CPythonListsort.Code.Policy.PendingLayout
/-!
# Pending-run correctness

This module joins the structural pending-stack invariant to the local
sortedness and occurrence-level stability facts needed by the later scan and
collapse proofs.  Origins are attached to the complete input before selecting
the consumed segment.  In particular, a run beginning away from index zero is
never retagged relative to its own beginning.
-/


namespace CPythonListsort

universe u v

/-- The occurrence-carrying keys currently stored in one pending run. -/
def pendingRunOccurrenceKeys (state : MergeState (Occurrence α) ν)
    (run : PendingRun) : Array (Occurrence α) :=
  (state.data.entries.extract run.base run.endIndex).map SortSliceEntry.key

/-- The occurrence-carrying keys of all pending runs, in stack/layout order. -/
def pendingOccurrenceKeys (state : MergeState (Occurrence α) ν) :
    List (Occurrence α) :=
  state.pending.toList.flatMap fun run =>
    (pendingRunOccurrenceKeys state run).toList

/-- Canonical tags for exactly `[base, base + scanned)` in the original input.

Tagging happens before extraction, so every retained origin is an absolute
index in `input`, rather than an index manufactured relative to this segment.
No element beyond the selected segment occurs in this definition. -/
def canonicalOccurrenceSegment (input : Array α) (base scanned : Nat) :
    List (Occurrence α) :=
  ((tagOccurrences input).extract base (base + scanned)).toList

/-- Correctness invariant for the already-consumed segment represented by the
pending stack.

It deliberately constrains neither the contents nor the order of the
unscanned suffix.  Comparator laws likewise remain outside the invariant and
are hypotheses only of the later preservation/correctness theorems. -/
def PendingRunsCorrect (lt : BoolComparator α) (input : Array α)
    (state : MergeState (Occurrence α) ν) (scanned : Nat) : Prop :=
  PendingLayout state scanned ∧
    (∀ run ∈ state.pending.toList,
      Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys state run)) ∧
    StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input state.basekeys scanned)
      (pendingOccurrenceKeys state)

namespace PendingRunsCorrect

/-! ## Absolute-origin regressions -/

def pendingRunsCorrectRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

def pendingRunsCorrectRegressionEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

def pendingRunsCorrectRegressionInput : Array Nat :=
  #[99, 7, 7, 777]

def pendingRunsCorrectSuffixInput : Array Nat :=
  #[99, 7, 7, 888]

/-- A concrete state whose one pending run covers the nonzero-base consumed
segment `[1, 3)`.  Equal keys retain their absolute origins one and two, while
index three is deliberately left unscanned. -/
def pendingRunsCorrectRegressionState :
    MergeState (Occurrence Nat) PUnit :=
  { min_gallop := 7
    listlen := 3
    basekeys := 1
    data :=
      { entries :=
          #[pendingRunsCorrectRegressionEntry 99 0,
            pendingRunsCorrectRegressionEntry 7 1,
            pendingRunsCorrectRegressionEntry 7 2,
            pendingRunsCorrectRegressionEntry 777 3] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[{ base := 1, len := 2, power := none }]
    key_compare := occurrenceComparator pendingRunsCorrectRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- The same state through the consumed endpoint, with only the unscanned
entry at absolute index three changed. -/
def pendingRunsCorrectSuffixState :
    MergeState (Occurrence Nat) PUnit :=
  { pendingRunsCorrectRegressionState with
    data :=
      { entries :=
          #[pendingRunsCorrectRegressionEntry 99 0,
            pendingRunsCorrectRegressionEntry 7 1,
            pendingRunsCorrectRegressionEntry 7 2,
            pendingRunsCorrectRegressionEntry 888 3] } }

end PendingRunsCorrect
end CPythonListsort
