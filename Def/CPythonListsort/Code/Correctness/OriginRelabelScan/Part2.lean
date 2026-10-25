/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean -/

import Structure.CPythonListsort.Code.Correctness.OriginRelabelMerges
import Structure.CPythonListsort.Code.Correctness.ScanLoopCorrectness
import Theorem.CPythonListsort.Code.Correctness.OriginRelabelScan
/-!
# Origin relabeling through policy and scan evaluators

This module continues `OriginRelabelMerges` through the raw `merge_at`,
PowerSort-policy, final-collapse, cleanup, and scan evaluators.  Occurrence
origins are proof metadata: every executable comparison observes only the
underlying value, so uniformly mirroring origins commutes with these
evaluators when the state's comparator is the lifted value comparator.

The statements here are deliberately about the raw, untraced evaluator.  The
trace model records concrete entries and therefore needs its own separately
reviewed transport argument.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-! ## Scan continuations -/

/-- The continuation shared by the binarysort and already-long-enough arms of
one scan iteration.  This is definitionally the tail of `listSortScan?`; naming
it keeps the origin-parametricity proof aligned with the evaluator's actual
control-flow boundary. -/
def listSortScanAfterExtension? (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize runLength : Nat) (extensionFuel : Bool) :
    Option (ListSortImplResult (Occurrence alpha) nu) :=
  let runLength := runLength
  let extensionFuel := extensionFuel
  if extensionFuel then
    finishListSort? state reverse inputSize (-1) true
  else if runLength = 0 ∨ remaining < runLength then
    none
  else
    match foundNewRun? state runLength with
    | none => none
    | some found =>
        if found.returnCode = 0 ∧ !found.fuelExhausted then
          let newRun : PendingRun :=
            { base := lo
              len := BitVec.ofNat 64 runLength
              power := none }
          let state := pushPendingRun found.state newRun
          listSortScan? fuel state (lo + runLength) (remaining - runLength)
            reverse inputSize
        else
          failFromFoundNewRun? found reverse inputSize

/-- The portion of one scan iteration following a successful natural-run
scan.  It is a definitional factorization of the corresponding `do`-block in
`listSortScan?`, not a second evaluator specification. -/
def listSortScanAfterCount? (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (counted : CountRunResult (Occurrence alpha) nu) :
    Option (ListSortImplResult (Occurrence alpha) nu) :=
  let state := { state with data := counted.slice }
  if counted.fuelExhausted then
    finishListSort? state reverse inputSize (-1) true
  else if counted.length = 0 ∨ remaining < counted.length then
    none
  else do
    let nextMinrun := minrunNext state.minrunState
    let state := installMinrunState state nextMinrun.state
    let runLength := counted.length
    let target := nextMinrun.result.toNat
    let force := if remaining ≤ target then remaining else target
    let extended ←
      if (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result then
        match binarysort? state state.data (Int.ofNat lo) force runLength with
        | none => none
        | some sorted => some (sorted.slice, force, sorted.fuelExhausted)
      else
        some (state.data, runLength, false)
    let state := { state with data := extended.1 }
    listSortScanAfterExtension? fuel state lo remaining reverse inputSize
      extended.2.1 extended.2.2

end CPythonListsort
