import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Correctness.PendingRunCorrectness
open CPythonListsort CPythonListsort.PendingRunsCorrect


namespace CPythonListsort.PendingRunsCorrect

/--
[layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean)
-/
@[path]
lemma layout
  {α : Type u}
  {ν : Type v}
  {lt : BoolComparator α}
  {input : Array α}
  {state : MergeState (Occurrence α) ν}
  {scanned : Nat}
-- given
  (h : PendingRunsCorrect lt input state scanned) :
-- imply
  PendingLayout state scanned :=
-- proof
  h.1

end CPythonListsort.PendingRunsCorrect

namespace CPythonListsort.PendingRunsCorrect

/--
[runSorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean)
-/
@[path]
lemma runSorted
  {α : Type u}
  {ν : Type v}
  {lt : BoolComparator α}
  {input : Array α}
  {state : MergeState (Occurrence α) ν}
  {scanned : Nat}
  {run : PendingRun}
-- given
  (h : PendingRunsCorrect lt input state scanned)
  (hrun : run ∈ state.pending.toList) :
-- imply
  Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys state run) :=
-- proof
  h.2.1 run hrun

end CPythonListsort.PendingRunsCorrect

namespace CPythonListsort.PendingRunsCorrect

/--
[stableOccurrencePermutation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean)
-/
@[path]
lemma stableOccurrencePermutation
  {α : Type u}
  {ν : Type v}
  {lt : BoolComparator α}
  {input : Array α}
  {state : MergeState (Occurrence α) ν}
  {scanned : Nat}
-- given
  (h : PendingRunsCorrect lt input state scanned) :
-- imply
  StableOccurrencePermutation lt (canonicalOccurrenceSegment input state.basekeys scanned) (pendingOccurrenceKeys state) :=
-- proof
  h.2.2

end CPythonListsort.PendingRunsCorrect

namespace CPythonListsort.PendingRunsCorrect

/--
[pending_perm_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean)
-/
@[path]
lemma pending_perm_canonical
  {α : Type u}
  {ν : Type v}
  {lt : BoolComparator α}
  {input : Array α}
  {state : MergeState (Occurrence α) ν}
  {scanned : Nat}
-- given
  (h : PendingRunsCorrect lt input state scanned) :
-- imply
  (pendingOccurrenceKeys state).Perm (canonicalOccurrenceSegment input state.basekeys scanned) :=
-- proof
  h.stableOccurrencePermutation.1

end CPythonListsort.PendingRunsCorrect

namespace CPythonListsort.PendingRunsCorrect

/--
[pending_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean)
-/
@[path]
lemma pending_stable
  {α : Type u}
  {ν : Type v}
  {lt : BoolComparator α}
  {input : Array α}
  {state : MergeState (Occurrence α) ν}
  {scanned : Nat}
-- given
  (h : PendingRunsCorrect lt input state scanned) :
-- imply
  (pendingOccurrenceKeys state).Pairwise fun (earlier later : Occurrence α) => ComparatorEquivalent lt earlier.value later.value → earlier.origin < later.origin :=
-- proof
  h.stableOccurrencePermutation.2

end CPythonListsort.PendingRunsCorrect

namespace CPythonListsort

/--
[pendingRunsCorrect_nonzeroBase_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean)
-/
@[path]
lemma pendingRunsCorrect_nonzeroBase_witness
-- imply
  PendingRunsCorrect pendingRunsCorrectRegressionLt pendingRunsCorrectRegressionInput pendingRunsCorrectRegressionState 2 := by
-- proof
  norm_num [PendingRunsCorrect, PendingLayout, PendingRunsCover,
    PendingRun.endIndex, pendingRunOccurrenceKeys, pendingOccurrenceKeys,
    canonicalOccurrenceSegment, StableOccurrencePermutation, Sorted,
    ComparatorEquivalent, occurrenceComparator, tagOccurrences,
    pendingRunsCorrectRegressionLt, pendingRunsCorrectRegressionInput,
    pendingRunsCorrectRegressionState, pendingRunsCorrectRegressionEntry,
    PySSize.Nonnegative, BitVec.toNat_ofNat, BitVec.msb, BitVec.getMsbD,
    BitVec.getLsbD]
  all_goals decide

end CPythonListsort

namespace CPythonListsort

/--
[pendingRunsCorrect_unscannedSuffix_freedom_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean)
-/
@[path]
lemma pendingRunsCorrect_unscannedSuffix_freedom_regression
-- imply
  pendingRunsCorrectRegressionInput.extract 0 3 = pendingRunsCorrectSuffixInput.extract 0 3 ∧ pendingRunsCorrectRegressionState.data.entries.extract 0 3 = pendingRunsCorrectSuffixState.data.entries.extract 0 3 ∧ pendingRunsCorrectRegressionInput ≠ pendingRunsCorrectSuffixInput ∧ pendingRunsCorrectRegressionState.data.entries ≠ pendingRunsCorrectSuffixState.data.entries ∧ canonicalOccurrenceSegment pendingRunsCorrectRegressionInput 1 2 = canonicalOccurrenceSegment pendingRunsCorrectSuffixInput 1 2 ∧ pendingOccurrenceKeys pendingRunsCorrectRegressionState = pendingOccurrenceKeys pendingRunsCorrectSuffixState ∧ PendingRunsCorrect pendingRunsCorrectRegressionLt pendingRunsCorrectRegressionInput pendingRunsCorrectRegressionState 2 ∧ PendingRunsCorrect pendingRunsCorrectRegressionLt pendingRunsCorrectSuffixInput pendingRunsCorrectSuffixState 2 := by
-- proof
  norm_num [PendingRunsCorrect, PendingLayout, PendingRunsCover,
    PendingRun.endIndex, pendingRunOccurrenceKeys, pendingOccurrenceKeys,
    canonicalOccurrenceSegment, StableOccurrencePermutation, Sorted,
    ComparatorEquivalent, occurrenceComparator, tagOccurrences,
    pendingRunsCorrectRegressionLt, pendingRunsCorrectRegressionInput,
    pendingRunsCorrectSuffixInput, pendingRunsCorrectRegressionState,
    pendingRunsCorrectSuffixState, pendingRunsCorrectRegressionEntry,
    PySSize.Nonnegative, BitVec.toNat_ofNat, BitVec.msb, BitVec.getMsbD,
    BitVec.getLsbD]
  all_goals decide

end CPythonListsort

namespace CPythonListsort

/--
[canonicalOccurrenceSegment_absolute_origins_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean)
-/
@[path]
lemma canonicalOccurrenceSegment_absolute_origins_regression
-- imply
  canonicalOccurrenceSegment (#[10, 20, 30] : Array Nat) 1 2 = [{ value := 20, origin := 1 }, { value := 30, origin := 2 }] := by
-- proof
  norm_num [canonicalOccurrenceSegment, tagOccurrences]

end CPythonListsort

namespace CPythonListsort

/--
[canonicalOccurrenceSegment_ne_local_retag_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/PendingRunCorrectness.lean)
-/
@[path]
lemma canonicalOccurrenceSegment_ne_local_retag_regression
-- imply
  canonicalOccurrenceSegment (#[10, 20, 30] : Array Nat) 1 2 ≠ (tagOccurrences ((#[10, 20, 30] : Array Nat).extract 1 3)).toList := by
-- proof
  norm_num [canonicalOccurrenceSegment, tagOccurrences]

end CPythonListsort


-- created on 2026-10-23
