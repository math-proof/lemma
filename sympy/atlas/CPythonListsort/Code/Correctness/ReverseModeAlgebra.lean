/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.OriginRelabelEquivariance

/-!
# Order and stability algebra for reverse mode

These lemmas contain no evaluator reasoning.  They formalize the mathematical
effect of CPython's reverse-before / stable-forward-sort / reverse-after
pattern once evaluator equivariance has supplied the mirrored pre-finish
result.
-/

namespace CPythonListsort

universe u

/-- The argument-swapped comparator requested by `reverse = true`. -/
def swappedComparator (lt : BoolComparator α) : BoolComparator α :=
  fun left right => lt right left

/-- Comparator selected by the public `reverse` flag. -/
def requestedComparator (lt : BoolComparator α) (reverse : Bool) :
    BoolComparator α :=
  if reverse then swappedComparator lt else lt

/-- Either public direction selected by the Boolean mode is again a strict
weak order. -/
theorem BoolStrictWeakOrder.requestedComparator
    {lt : BoolComparator α} (h : BoolStrictWeakOrder lt) (reverse : Bool) :
    BoolStrictWeakOrder (requestedComparator lt reverse) := by
  cases reverse
  · simpa using h
  · simpa using h.swapped

/-- Comparator equivalence is unchanged when the comparator arguments are
swapped. -/
theorem comparatorEquivalent_swapped (lt : BoolComparator α) (left right : α) :
    ComparatorEquivalent (swappedComparator lt) left right ↔
      ComparatorEquivalent lt left right := by
  simp [ComparatorEquivalent, swappedComparator, and_comm]

/-- A sequence with descending origins inside each comparator-equivalence
class.  This is the natural intermediate stability contract after origin
mirroring but before CPython's final whole-array reversal. -/
def ReverseStableOccurrencePermutation (lt : BoolComparator α)
    (canonical output : List (Occurrence α)) : Prop :=
  output.Perm canonical ∧
    output.Pairwise fun earlier later =>
      ComparatorEquivalent lt earlier.value later.value →
        later.origin < earlier.origin

namespace ReverseStableOccurrencePermutation

/-- Reversing the output turns reverse stability into ordinary stability for
the argument-swapped comparator; the canonical sequence is used only through
permutation and therefore remains unchanged. -/
theorem reverse
    {lt : BoolComparator α} {canonical output : List (Occurrence α)}
    (h : ReverseStableOccurrencePermutation lt canonical output) :
    StableOccurrencePermutation (swappedComparator lt) canonical
      output.reverse := by
  constructor
  · exact output.reverse_perm.trans h.1
  · rw [List.pairwise_reverse]
    apply h.2.imp
    intro earlier later hstable hequivalent
    rw [comparatorEquivalent_swapped] at hequivalent
    exact hstable ⟨hequivalent.2, hequivalent.1⟩

end ReverseStableOccurrencePermutation

/-- Reverse the physical paired-entry array, keeping each key attached to its
optional payload. -/
def reverseEntries (slice : SortSlice κ ν) : SortSlice κ ν :=
  { entries := slice.entries.reverse }

/-- Reversal cannot change keyed/unkeyed payload representation mode. -/
theorem ValuesModeInvariant.reverseEntries
    {hasKeyfunc : Bool} {slice : SortSlice κ ν}
    (h : ValuesModeInvariant hasKeyfunc slice) :
    ValuesModeInvariant hasKeyfunc slice.reverseEntries := by
  intro index hindex
  have hindex' : index < slice.entries.size := by
    simpa [reverseEntries] using hindex
  have hsource : slice.entries.size - 1 - index < slice.entries.size := by
    omega
  simpa [reverseEntries] using
    h (slice.entries.size - 1 - index) hsource

end SortSlice

namespace ListSortInput

/-- A validated top-level input with its complete paired-entry array reversed. -/
def reverseEntries (input : ListSortInput κ ν) : ListSortInput κ ν where
  slice := input.slice.reverseEntries
  hasKeyfunc := input.hasKeyfunc
  valuesMode := input.valuesMode.reverseEntries
