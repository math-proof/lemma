/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Mathlib.Data.List.Sort
import Def.CPythonListsort.Code.Assembly.Order.Part2
/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/


namespace CPythonListsort

universe u

/-- Strict-weak-order laws lift through occurrence tagging because the
comparator deliberately ignores the immutable origin field.  Merge and scan
correctness use this public bridge when applying order theorems to the actual
tagged keys moved by the transcription. -/
theorem BoolStrictWeakOrder.occurrenceComparator
    {lt : BoolComparator α} (h : BoolStrictWeakOrder lt) :
    BoolStrictWeakOrder (occurrenceComparator lt) := by
  exact
    { toIsStrictWeakOrder :=
        { toIsStrictOrder :=
            { toIrrefl := ⟨fun occurrence => h.irrefl occurrence.value⟩
              toIsTrans :=
                ⟨fun first second third hfirstSecond hsecondThird =>
                  h.trans first.value second.value third.value hfirstSecond
                    hsecondThird⟩ }
          incomp_trans := fun first second third hfirstSecond hsecondThird =>
            h.incomp_trans first.value second.value third.value hfirstSecond
              hsecondThird } }

end CPythonListsort
