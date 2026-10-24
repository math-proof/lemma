import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Correctness.ReverseSliceCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.SortSliceRange
open CPythonListsort


namespace CPythonListsort.ReverseRangeSpec

/--
[sortSliceRangeEntries_reverseRange_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseRangeSupport.lean)
-/
@[path]
lemma sortSliceRangeEntries_reverseRange_self
  {slice : SortSlice κ ν}
  {start count : Nat}
-- given
  (hstop : start + count ≤ slice.entries.size) :
-- imply
  sortSliceRangeEntries ({ entries := reverseRangeEntries slice.entries start (start + count) } : SortSlice κ ν) start count = (sortSliceRangeEntries slice start count).reverse := by
-- proof
  apply Array.toList_inj.mp
  rw [sortSliceRangeEntries_toList, Array.toList_reverse,
    sortSliceRangeEntries_toList]
  rw [toList_reverseRange]
  have hstartLength :
    (slice.entries.toList.take start).length = start := by
    simp
    omega
  have hmiddleLength :
    ((slice.entries.toList.drop start).take count).length = count := by
    simp
    omega
  simp [hstartLength, hmiddleLength]

end CPythonListsort.ReverseRangeSpec

namespace CPythonListsort.ReverseRangeSpec

/--
[sortSliceRangeKeys_reverseRange_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseRangeSupport.lean)
-/
@[path]
lemma sortSliceRangeKeys_reverseRange_self
  {slice : SortSlice κ ν}
  {start count : Nat}
-- given
  (hstop : start + count ≤ slice.entries.size) :
-- imply
  sortSliceRangeKeys ({ entries := reverseRangeEntries slice.entries start (start + count) } : SortSlice κ ν) start count = (sortSliceRangeKeys slice start count).reverse := by
-- proof
  simp only [sortSliceRangeKeys]
  rw [sortSliceRangeEntries_reverseRange_self slice start count hstop]
  simp

end CPythonListsort.ReverseRangeSpec

namespace CPythonListsort.ReverseRangeSpec

/--
[equalOutsideRange_reverseRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseRangeSupport.lean)
-/
@[path]
lemma equalOutsideRange_reverseRange
  {slice : SortSlice κ ν}
  {start count : Nat}
-- given
  (hstop : start + count ≤ slice.entries.size) :
-- imply
  SortSlice.EqualOutsideRange slice ({ entries := reverseRangeEntries slice.entries start (start + count) } : SortSlice κ ν) start count := by
-- proof
  have hsize := size_reverseRange slice.entries start (start + count)
    (by omega) hstop
  refine ⟨hsize.symm, ?_⟩
  intro otherStart otherCount hdisjoint
  apply Array.ext_getElem?
  intro offset
  simp only [sortSliceRangeEntries, Array.getElem?_extract, hsize]
  by_cases hoff :
    offset < min (otherStart + otherCount) slice.entries.size - otherStart
  · rw [if_pos hoff, if_pos hoff]
    obtain hbefore | hafter := hdisjoint
    · rw [getElem?_reverseRange_before slice.entries start (start + count)
      (otherStart + offset) (by omega) hstop (by omega)]
    · rw [getElem?_reverseRange_after slice.entries start (start + count)
      (otherStart + offset) (by omega) hstop (by omega)]
  · rw [if_neg hoff, if_neg hoff]

end CPythonListsort.ReverseRangeSpec


-- created on 2026-10-23
