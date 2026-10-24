/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ListSortCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.ScanLoopCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.ReverseModeCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.OccurrenceErasureScan

/-!
# Public functional correctness of listsort

This module packages correctness at the proof-carrying `ListSortInput`
boundary.  The implementation sorts occurrence-tagged keys so origins travel
through every modeled movement; the final post exposes requested-order
sortedness, occurrence-level stability, and the whole key/payload snapshot.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- The complete implementation-level functional-correctness certificate.

`rawResultEq` is deliberately part of the public post: the semantic facts are
about the result returned by the transcribed evaluator, not an independently
constructed sorted array.  `entrySnapshot` retains keyed payload pairing in
addition to the key-facing sortedness and stability clauses. -/
structure ListSortCorrectnessPost
    (lt : BoolComparator alpha) (reverse : Bool)
    (input : ListSortInput alpha nu)
    (result : ListSortImplResult (Occurrence alpha) nu) : Prop where
  rawResultEq :
    listSort? (occurrenceComparator lt) reverse input.withOccurrenceKeys =
      some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  sorted :
    Sorted (occurrenceComparator (requestedComparator lt reverse))
      result.occurrences
  stable :
    StableOccurrencePermutation (requestedComparator lt reverse)
      (tagOccurrences
        (input.slice.entries.map SortSliceEntry.key)).toList
      result.occurrences.toList
  entrySnapshot : EntrySnapshotPermutation input.slice result.state.data

/-! ## Inhabited boundary witnesses -/

private def correctnessRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def reverseKeyedDuplicateInput : ListSortInput Nat Nat :=
  ListSortInput.keyed #[(2, 20), (1, 10), (1, 11), (2, 21)]

private structure CorrectnessRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

private def correctnessRegressionView
    (result : ListSortImplResult (Occurrence Nat) Nat) :
    CorrectnessRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    entries := result.state.data.entries.toList.map fun entry =>
      (entry.key.value, entry.key.origin, entry.value) }
