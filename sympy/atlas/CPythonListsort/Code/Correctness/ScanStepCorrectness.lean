/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.ListSortTermination
import sympy.atlas.CPythonListsort.Code.Correctness.BinarysortCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.CountRunCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.FoundNewRunCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.ScanCorrectnessSupport
import sympy.atlas.CPythonListsort.Code.Correctness.ScanStepSupport

/-!
# Correctness of one forward scan iteration

This module stops at the recursive-call boundary of `listSortScan?`.  It
combines the already-reviewed safety invariant with pending-run correctness,
the whole-entry unscanned snapshot, and the persistent input permutation.
-/

namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

/-- Full induction invariant for the occurrence-carrying forward scan. -/
structure ListSortScanCorrectnessInvariant
    (lt : BoolComparator α) (source : SortSlice α ν) (hasKeyfunc : Bool)
    (inputSize : Nat) (state : MergeState (Occurrence α) ν)
    (lo scanned remaining : Nat) : Prop where
  safety : ListSortScanInvariant (occurrenceComparator lt) hasKeyfunc inputSize
    state lo scanned remaining
  pendingRunsCorrect : PendingRunsCorrect lt
    (source.entries.map SortSliceEntry.key) state scanned
  remainderEntries : ScanRemainderEntriesMatch source state scanned
  entrySnapshot : EntrySnapshotPermutation source state.data

/-- Observable result of exactly one nonterminal scan iteration.  The equation
mentions the real raw evaluator and exposes the precise recursive call. -/
structure ListSortScanStepCorrectnessPost
    (lt : BoolComparator α) (source : SortSlice α ν) (hasKeyfunc : Bool)
    (inputSize fuel : Nat) (state : MergeState (Occurrence α) ν)
    (lo scanned remaining : Nat) (reverse : Bool)
    (consumed : Nat) (nextState : MergeState (Occurrence α) ν) : Prop where
  consumedPositive : 0 < consumed
  consumedWithin : consumed ≤ remaining
  consumedPrefixFrame : SortSlice.EqualOutsideRange state.data nextState.data
    state.basekeys (scanned + consumed)
  scanEquation :
    listSortScan? (fuel + 1) state lo remaining reverse inputSize =
      listSortScan? fuel nextState (lo + consumed) (remaining - consumed)
        reverse inputSize
  nextInvariant : ListSortScanCorrectnessInvariant lt source hasKeyfunc
    inputSize nextState (lo + consumed) (scanned + consumed)
      (remaining - consumed)

/-- Abstract form of the `foundNewRun_correct` call used by the step proof.
The concrete public theorem below instantiates this provider; keeping the core
parameterized also makes the merge dependency explicit. -/
private def FoundNewRunCorrectnessProvider
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν) : Prop :=
  ∀ (state : MergeState (Occurrence α) ν) (scanned : Nat)
    (newRun : PendingRun),
    PendingRunsCorrect lt input state scanned →
    EntrySnapshotPermutation source state.data →
    state.key_compare = occurrenceComparator lt →
    state.listlen.toNat ≤ PY_LIST_MAX →
    PoweredPrefix state →
    newRun.base = state.basekeys + scanned →
    newRun.len.Nonnegative →
    0 < newRun.len.toNat →
    scanned + newRun.len.toNat ≤ state.listlen.toNat →
    TempStorageInv state.a state.alloced →
    state.a.Live →
    SortSlice.ValuesModeInvariant state.a.hasValues state.data →
    ∃ result,
      FoundNewRunCorrectnessPost lt input source state scanned newRun result

/-- Internal boundary between run formation (`count_run` plus optional
`binarysort`) and the policy/push phase.  The explicit `stable` field is the
whole-target premise/output at the binarysort boundary. -/
private structure ListSortRunFormationPost
    (lt : BoolComparator α) (source : SortSlice α ν) (hasKeyfunc : Bool)
    (inputSize fuel : Nat) (call : MergeState (Occurrence α) ν)
    (lo scanned remaining : Nat) (reverse : Bool)
    (formed : MergeState (Occurrence α) ν) (consumed : Nat) : Prop where
  positive : 0 < consumed
  within : consumed ≤ remaining
  listlen : formed.listlen = call.listlen
  basekeys : formed.basekeys = call.basekeys
  extent : formed.data.entries.size = call.data.entries.size
  hasValues : formed.a.hasValues = call.a.hasValues
  comparator : formed.key_compare = call.key_compare
  tempInvariant : TempStorageInv formed.a formed.alloced
  tempLive : formed.a.Live
  physicalBound :
    (MergeMemorySnapshot.ofState formed).PhysicalBound
  valuesMode : SortSlice.ValuesModeInvariant formed.a.hasValues formed.data
  poweredPrefix : PoweredPrefix formed
  pendingRunsCorrect : PendingRunsCorrect lt
    (source.entries.map SortSliceEntry.key) formed scanned
  entrySnapshot : EntrySnapshotPermutation source formed.data
  frame : SortSlice.EqualOutsideRange call.data formed.data
    (call.basekeys + scanned) consumed
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys formed.data (call.basekeys + scanned) consumed)
  stable : StableOccurrencePermutation lt
    (canonicalOccurrenceSegment (source.entries.map SortSliceEntry.key)
      (call.basekeys + scanned) consumed)
    (sortSliceRangeKeys formed.data
      (call.basekeys + scanned) consumed).toList
  adaptiveAfter : 0 < remaining - consumed →
    ∃ calls, AdaptiveMinrunScanInvariant formed.listlen calls
      (scanned + consumed) formed.minrunState
  scanEquationBeforeFound :
    listSortScan? (fuel + 1) call lo remaining reverse inputSize =
      listSortAfterExtension?
        (fun nextState nextLo nextRemaining =>
          listSortScan? fuel nextState nextLo nextRemaining reverse inputSize)
        lo remaining reverse inputSize (formed, consumed, false)

/-! ## Concrete branch witnesses -/

private def scanStepRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def scanStepRegressionEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := value, origin := origin }, value := some payload }

private def scanStepExtensionSlice : SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[scanStepRegressionEntry 99 0 10,
        scanStepRegressionEntry 3 1 11,
        scanStepRegressionEntry 1 2 12,
        scanStepRegressionEntry 2 3 13,
        scanStepRegressionEntry 0 4 14,
        scanStepRegressionEntry 77 5 15] }

private def scanStepExtensionState : MergeState (Occurrence Nat) Nat :=
  (initialMergeState (occurrenceComparator scanStepRegressionLt) true
    scanStepExtensionSlice).1

private structure ScanStepExtensionRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  pending : List (Nat × Nat)
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

private def scanStepExtensionRegressionView
    (result : ListSortImplResult (Occurrence Nat) Nat) :
    ScanStepExtensionRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    pending := result.state.pending.toList.map (fun run =>
      (run.base, run.len.toNat))
    entries := result.state.data.entries.toList.map (fun entry =>
      (entry.key.value, entry.key.origin, entry.value)) }

private def scanStepExtensionRegressionExpected :
    ScanStepExtensionRegressionView :=
  { returnCode := 0
    fuelExhausted := false
    pending := [(1, 4)]
    entries :=
      [(99, 0, some 10), (0, 4, some 14), (1, 2, some 12),
       (2, 3, some 13), (3, 1, some 11), (77, 5, some 15)] }

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in

private def scanStepNoExtensionSlice : SortSlice (Occurrence Nat) PUnit :=
  { entries := (Array.range 64).map fun index =>
      ({ key := { value := index, origin := index }, value := none } :
        SortSliceEntry (Occurrence Nat) PUnit) }

private def scanStepNoExtensionState : MergeState (Occurrence Nat) PUnit :=
  let initialized :=
    (initialMergeState (occurrenceComparator scanStepRegressionLt) false
      scanStepNoExtensionSlice).1
  { initialized with
    pending := #[{ base := 0, len := BitVec.ofNat 64 24, power := none }] }

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in

private def scanStepPolicyMergeEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

private def scanStepPolicyMergeState : MergeState (Occurrence Nat) PUnit :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[scanStepPolicyMergeEntry 2 0,
            scanStepPolicyMergeEntry 1 1,
            scanStepPolicyMergeEntry 3 2] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 3 },
        { base := 1, len := 1, power := none }]
    key_compare := occurrenceComparator scanStepRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
