/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Mathlib.Data.List.Sort
import Structure.CPythonListsort.Code.Assembly.Order.Part3
/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/


namespace CPythonListsort

universe u

/-- Erase carried origin tags to obtain the externally observable values. -/
def TaggedOutput.values (ys : TaggedOutput α) : Array α :=
  ys.occurrences.map Occurrence.value

/-- The tagged input from which a sorting execution starts.  Sorting code must
move these records, rather than manufacture origins after producing values. -/
def TaggedOutput.fromInput (xs : Array α) : TaggedOutput α :=
  ⟨tagOccurrences xs⟩

/-- Occurrence-level stability.  The permutation clause ties every final tag
to the canonical tag attached to the input, while the pairwise clause keeps
comparator-equivalent occurrences in increasing original-index order. -/
def Stable (lt : BoolComparator α) (xs : Array α) (ys : TaggedOutput α) : Prop :=
  StableOccurrencePermutation lt (tagOccurrences xs).toList
    ys.occurrences.toList

end CPythonListsort
