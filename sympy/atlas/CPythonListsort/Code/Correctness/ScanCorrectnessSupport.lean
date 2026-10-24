/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanCorrectnessSupport.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.ScanRemainder
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeTopPowerPreservation

/-!
# Support lemmas for forward scan correctness

This module collects comparator-independent range and frame lemmas, together
with the absolute-origin stability composition used by the forward scan proof.
It deliberately does not state the scan-step theorem itself.
-/

namespace CPythonListsort

universe u v

/-- An absolute-origin canonical segment splits at an adjacent subrange
boundary. -/
theorem canonicalOccurrenceSegment_add (input : Array α) (base left right : Nat) :
    canonicalOccurrenceSegment input base (left + right) =
      canonicalOccurrenceSegment input base left ++
        canonicalOccurrenceSegment input (base + left) right := by
  simp [canonicalOccurrenceSegment, List.extract, List.take_add, List.drop_drop]

/-- Absolute tagging makes every canonical segment pairwise stable relative to
itself: later list positions have strictly later absolute origins. -/
theorem canonicalOccurrenceSegment_pairwise_stable
    (lt : BoolComparator α) (input : Array α) (base count : Nat) :
    (canonicalOccurrenceSegment input base count).Pairwise fun earlier later =>
      ComparatorEquivalent lt earlier.value later.value →
        earlier.origin < later.origin := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij _
  simp [canonicalOccurrenceSegment, tagOccurrences] at hi hj ⊢
  omega

/-- Stable permutations of two adjacent absolute-origin segments append to a
stable permutation of their union.  Cross-segment comparator-equivalent pairs
are stable because every origin in the left segment is strictly before every
origin in the right segment. -/
theorem stableOccurrencePermutation_append_adjacent
    {lt : BoolComparator α} {input : Array α}
    {base leftCount rightCount : Nat}
    {left right : List (Occurrence α)}
    (hleft : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input base leftCount) left)
    (hright : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input (base + leftCount) rightCount) right) :
    StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input base (leftCount + rightCount))
      (left ++ right) := by
  rw [canonicalOccurrenceSegment_add]
  refine ⟨hleft.1.append hright.1, ?_⟩
  apply List.pairwise_append.mpr
  refine ⟨hleft.2, hright.2, ?_⟩
  have hcanonical :
      (canonicalOccurrenceSegment input base leftCount ++
        canonicalOccurrenceSegment input (base + leftCount) rightCount).Pairwise
          (fun earlier later =>
            ComparatorEquivalent lt earlier.value later.value →
              earlier.origin < later.origin) := by
    rw [← canonicalOccurrenceSegment_add]
    exact canonicalOccurrenceSegment_pairwise_stable lt input base
      (leftCount + rightCount)
  have hcross := (List.pairwise_append.mp hcanonical).2.2
  intro earlier hearlier later hlater
  exact hcross earlier (hleft.1.mem_iff.mp hearlier)
    later (hright.1.mem_iff.mp hlater)

namespace ScanRemainderEntriesMatch
