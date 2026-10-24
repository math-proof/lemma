/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.Order
import sympy.atlas.CPythonListsort.Code.Correctness.DescendingRunNormalization

/-!
# Stable-order invariant for `count_run`'s descending phase

This file contains only pure list/order algebra.  The executable count-run
proof instantiates it with the range read from the transcribed machine.
-/

namespace CPythonListsort

universe u

namespace DescendingRunSpec

/-- Pairwise relation corresponding to ascending `Sorted` order on occurrence
lists: a later occurrence must not compare strictly before an earlier one. -/
def SortedRelation (lt : BoolComparator α) :
    Occurrence α → Occurrence α → Prop :=
  fun earlier later => occurrenceComparator lt later earlier = false

/-- Pairwise occurrence-stability relation shared with
`StableOccurrencePermutation`. -/
def StableRelation (lt : BoolComparator α) :
    Occurrence α → Occurrence α → Prop :=
  fun earlier later =>
    ComparatorEquivalent lt earlier.value later.value →
      earlier.origin < later.origin

/-- The semantic state carried through `count_run`'s descending scan.

`normalize current tailLength` is the stable ascending sequence that would be
obtained by closing the current equality block and reversing the whole scanned
prefix. -/
structure Invariant (lt : BoolComparator α)
    (canonical current : List (Occurrence α)) (tailLength : Nat) : Prop where
  current_ne : current ≠ []
  tail_pos : 0 < tailLength
  tail_le : tailLength ≤ current.length
  sorted : (normalize current tailLength).Pairwise (SortedRelation lt)
  stable : StableOccurrencePermutation lt canonical
    (normalize current tailLength)
  tail_equiv :
    ∀ x ∈ (normalize current tailLength).take tailLength,
      ComparatorEquivalent lt x.value (current.getLast current_ne).value
  rest_greater :
    ∀ x ∈ (normalize current tailLength).drop tailLength,
      lt (current.getLast current_ne).value x.value = true

/-! ## Inhabited regression -/

private def descendingInvariantRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def descendingInvariantThree : Occurrence Nat :=
  { value := 3, origin := 0 }

private def descendingInvariantTwoOne : Occurrence Nat :=
  { value := 2, origin := 1 }

private def descendingInvariantTwoTwo : Occurrence Nat :=
  { value := 2, origin := 2 }
