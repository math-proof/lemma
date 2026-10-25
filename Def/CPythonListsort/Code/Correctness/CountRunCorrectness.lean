/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/CountRunCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.CountRunSafety.Part3
import Def.CPythonListsort.Code.Assembly.Order.Part4
import Structure.CPythonListsort.Code.Correctness.ReverseSliceCorrectness
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.DescendingRunNormalization
import Def.CPythonListsort.Code.Correctness.DescendingRunInvariant.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Correctness.ReverseRangeSupport
import Def.CPythonListsort.Code.Correctness.ScanRemainder.Part3
/-!
# Functional correctness of `count_run`

This file proves that the actual bounded `countRun?` transcription returns a
nonempty sorted run, preserves whole key/payload entries, and preserves the
origin order of comparator-equivalent occurrences.  The public theorem is
tied to `countRunTraced?` through the reviewed `countRun_safe` exact-erasure
certificate; no second run detector is substituted for the transcribed one.

The descending case follows CPython's two-level reversal literally.  Equal
blocks are reversed as the scan discovers them, the final equal block is
reversed at the boundary, and then the complete descending prefix is
reversed.  Thus the temporary order inside equal blocks is not exposed by the
public postcondition.
-/


namespace CPythonListsort

universe u v w x

variable {alpha : Type u} {nu : Type v}

variable {beta : Type w} {rho : Type x}

/-- The input-side condition needed for occurrence stability: within the
remaining source range, comparator-equivalent occurrences already appear in
increasing origin order.  The permutation half is deliberately the reflexive
one, so this is the shared `StableOccurrencePermutation` predicate rather
than a weaker local surrogate. -/
def CountRunCanonicalRange (lt : BoolComparator alpha)
    (slice : SortSlice (Occurrence alpha) nu) (base count : Nat) : Prop :=
  let canonical := (sortSliceRangeKeys slice base count).toList
  StableOccurrencePermutation lt canonical canonical

end CPythonListsort
