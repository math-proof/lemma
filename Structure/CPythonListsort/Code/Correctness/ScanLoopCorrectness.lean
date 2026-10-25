/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanLoopCorrectness.lean -/

import Def.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part3
/-!
# Correctness of the complete scan and final collapse

This module closes the induction left deliberately open by
`listSortScan_step_correct`.  It follows the actual `listSortScan?` recursion,
uses strict progress to show that the supplied fuel reaches the terminal arm,
and applies `mergeForceCollapse_correct` to the real terminal state.  The
public post retains that pre-finish collapse result, passes an arbitrary
`reverse` flag to the actual cleanup call, and records the successful scan
result.  A separate corollary exposes the simpler forward cleanup state.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Complete correctness certificate for a `listSortScan?` execution.

`terminal` is the state at the real `remaining = 0` call, `collapsed` is the
result returned by the real `mergeForceCollapse?` invocation there, and
`result` is the state after the requested final-reverse/cleanup phase. Retaining
all three keeps the pre-finish sorted/stable run available even though final
reversal changes its order and cleanup may release temporary storage. -/
structure ListSortScanCollapseCorrectnessPost
    (lt : BoolComparator alpha) (source : SortSlice alpha nu)
    (hasKeyfunc : Bool) (inputSize fuel : Nat)
    (state : MergeState (Occurrence alpha) nu)
    (lo scanned remaining : Nat) (reverse : Bool)
    (terminal : MergeState (Occurrence alpha) nu)
    (collapsed : MergeForceCollapseResult (Occurrence alpha) nu)
    (result : ListSortImplResult (Occurrence alpha) nu) : Prop where
  terminalInvariant : ListSortScanCorrectnessInvariant lt source hasKeyfunc
    inputSize terminal inputSize inputSize 0
  collapseCorrectness : MergeForceCollapseCorrectnessPost lt
    (source.entries.map SortSliceEntry.key) source terminal inputSize collapsed
  collapseResultEq : mergeForceCollapse? terminal = some collapsed
  preFinishEquation :
    listSortScan? fuel state lo remaining reverse inputSize =
      finishListSort? collapsed.state reverse inputSize 0 false
  resultEq :
    listSortScan? fuel state lo remaining reverse inputSize = some result
  finishResultEq :
    finishListSort? collapsed.state reverse inputSize 0 false = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  finalRun :
    ∃ run,
      collapsed.state.pending.toList = [run] ∧
      run.base = terminal.basekeys ∧
      run.endIndex = terminal.basekeys + inputSize ∧
      Sorted (occurrenceComparator lt)
        (pendingRunOccurrenceKeys collapsed.state run) ∧
      StableOccurrencePermutation lt
        (canonicalOccurrenceSegment
          (source.entries.map SortSliceEntry.key) terminal.basekeys inputSize)
        (pendingRunOccurrenceKeys collapsed.state run).toList
  collapsedSnapshot : EntrySnapshotPermutation source collapsed.state.data

end CPythonListsort
