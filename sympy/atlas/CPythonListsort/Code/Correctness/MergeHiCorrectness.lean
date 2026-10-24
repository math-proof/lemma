/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeHiCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.EntrySnapshotPermutation
import sympy.atlas.CPythonListsort.Code.Correctness.MergeHiInvariant

/-!
# Public functional postcondition for `merge_hi`

The physical algorithm fills its output from right to left, but its observable
specification is the ordinary forward, left-biased `stableEntryMerge` of the
two post-trimming input runs.  Keeping the exact whole-entry equality in the
public postcondition makes sortedness, occurrence stability, payload
permutation, framing, and persistent input snapshots consequences of one
semantic result rather than independent key-only claims.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Functional correctness certificate for the exact traced `merge_hi`
execution selected by `prepareMergeAt?`.

`exactRange` is the central result: the affected whole-entry range is exactly
the shared left-biased mathematical merge.  The remaining fields expose the
standard public sortedness, stability, whole-entry permutation, and frame
interfaces without asking downstream clients to unfold that target. -/
structure MergeHiCorrectnessPost
    (lt : BoolComparator alpha) (canonical : List (Occurrence alpha))
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeHiResult (Occurrence alpha) nu) : Prop where
  safety : MergeHiSafetyPost pre scanned i call
    (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeHiTargetEntries lt call
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb))
  stable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb)).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList.Perm
      (sortSliceRangeEntries call.state.data call.ssa.toNat
        (call.na + call.nb)).toList
  frame : SortSlice.EqualOutsideRange call.state.data result.state.data
    call.ssa.toNat (call.na + call.nb)

/-- Functional portion proved against the untraced transcription.  Separating
this certificate from `MergeHiSafetyPost` keeps the reverse-loop induction
focused on whole-entry movement while the public join below identifies its
result with the actual traced execution by exact erasure. -/
structure MergeHiRawCorrectnessPost
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeHiResult (Occurrence alpha) nu) : Prop where
  resultEq : mergeHi? call.state call.ssa call.ssb call.na call.nb = some result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeHiTargetEntries lt call
  frame : SortSlice.EqualOutsideRange call.state.data result.state.data
    call.ssa.toNat (call.na + call.nb)

/-! ## Raw reverse-loop correctness -/

/-- The two semantic facts carried from a live reverse-fill cursor to a
successful raw result. -/
def MergeHiSemanticResult
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeHiResult (Occurrence alpha) nu) : Prop :=
  (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeHiTargetEntries lt call ∧
    SortSlice.EqualOutsideRange call.state.data result.state.data
      call.ssa.toNat (call.na + call.nb)

/-- Semantic contract required of the recursive continuation passed to a
single galloping round. -/
def MergeHiSemanticContinuation
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (next : MergeHiCursor (Occurrence alpha) nu →
      Option (MergeHiResult (Occurrence alpha) nu)) : Prop :=
  ∀ cursor result, MergeHiSemanticCursorInvariant lt call cursor →
    next cursor = some result → result.fuelExhausted = false →
      MergeHiSemanticResult lt call result

/-! ## Executable exact-target regression -/

private def mergeHiCorrectnessNatLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def mergeHiCorrectnessEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := value, origin := origin }, value := some payload }

/-- A keyed fixture with one cell on each side of the affected range.  The
equal `4` occurrences straddle the two runs, so the expected stable merge also
checks the reverse-fill tie direction and whole-entry payload pairing. -/
private def mergeHiCorrectnessRegressionState :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data :=
      { entries :=
          #[mergeHiCorrectnessEntry 99 0 990,
            mergeHiCorrectnessEntry 4 1 40,
            mergeHiCorrectnessEntry 5 2 50,
            mergeHiCorrectnessEntry 1 3 11,
            mergeHiCorrectnessEntry 4 4 41,
            mergeHiCorrectnessEntry 100 5 1000] }
    a :=
      { cells := Array.replicate 2 none
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := occurrenceComparator mergeHiCorrectnessNatLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def mergeHiCorrectnessRegressionExpectedState :
    MergeState (Occurrence Nat) Nat :=
  { mergeHiCorrectnessRegressionState with
    data :=
      { entries :=
          #[mergeHiCorrectnessEntry 99 0 990,
            mergeHiCorrectnessEntry 1 3 11,
            mergeHiCorrectnessEntry 4 1 40,
            mergeHiCorrectnessEntry 4 4 41,
            mergeHiCorrectnessEntry 5 2 50,
            mergeHiCorrectnessEntry 100 5 1000] }
    a :=
      { cells :=
          #[some (mergeHiCorrectnessEntry 1 3 11),
            some (mergeHiCorrectnessEntry 4 4 41)]
        backing := .inline
        hasValues := true } }

private def mergeHiCorrectnessRegressionExpectedResult :
    MergeHiResult (Occurrence Nat) Nat :=
  { state := mergeHiCorrectnessRegressionExpectedState
    returnCode := 0
    fuelExhausted := false }
