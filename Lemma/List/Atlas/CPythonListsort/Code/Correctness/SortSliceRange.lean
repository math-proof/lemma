import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Correctness.SortSliceRange
open CPythonListsort CPythonListsort.SortSlice CPythonListsort.SortSlice.EqualOutsideRange


namespace CPythonListsort

/--
[sortSliceRangeKeys_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeKeys_eq_map
  {slice : SortSlice κ ν}
  {start count : Nat} :
-- imply
  sortSliceRangeKeys slice start count = (sortSliceRangeEntries slice start count).map SortSliceEntry.key :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeEntries_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeEntries_zero
  {slice : SortSlice κ ν}
  {start : Nat} :
-- imply
  sortSliceRangeEntries slice start 0 = #[] := by
-- proof
  simp [sortSliceRangeEntries]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeKeys_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeKeys_zero
  {slice : SortSlice κ ν}
  {start : Nat} :
-- imply
  sortSliceRangeKeys slice start 0 = #[] := by
-- proof
  simp [sortSliceRangeKeys]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeEntries_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeEntries_size
  {slice : SortSlice κ ν}
  {start count : Nat}
-- given
  (hstop : start + count ≤ slice.entries.size) :
-- imply
  (sortSliceRangeEntries slice start count).size = count := by
-- proof
  simp [sortSliceRangeEntries]
  omega

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeKeys_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeKeys_size
  {slice : SortSlice κ ν}
  {start count : Nat}
-- given
  (hstop : start + count ≤ slice.entries.size) :
-- imply
  (sortSliceRangeKeys slice start count).size = count := by
-- proof
  simp [sortSliceRangeKeys, sortSliceRangeEntries_size _ _ _ hstop]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeEntries_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeEntries_getElem
  {slice : SortSlice κ ν}
  {start count i : Nat}
-- given
  (hstop : start + count ≤ slice.entries.size)
  (hi : i < count) :
-- imply
  (sortSliceRangeEntries slice start count)[i]'(by rw [sortSliceRangeEntries_size slice start count hstop] exact hi) = slice.entries[start + i]'(by omega) := by
-- proof
  simp only [sortSliceRangeEntries]
  rw [Array.getElem_extract]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeKeys_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeKeys_getElem
  {slice : SortSlice κ ν}
  {start count i : Nat}
-- given
  (hstop : start + count ≤ slice.entries.size)
  (hi : i < count) :
-- imply
  (sortSliceRangeKeys slice start count)[i]'(by rw [sortSliceRangeKeys_size slice start count hstop] exact hi) = (slice.entries[start + i]'(by omega)).key := by
-- proof
  simp only [sortSliceRangeKeys, sortSliceRangeEntries, Array.getElem_map]
  rw [Array.getElem_extract]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeEntries_toList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeEntries_toList
  {slice : SortSlice κ ν}
  {start count : Nat} :
-- imply
  (sortSliceRangeEntries slice start count).toList = (slice.entries.toList.drop start).take count := by
-- proof
  simp [sortSliceRangeEntries, List.extract]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeEntries_toList_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeEntries_toList_add
  {slice : SortSlice κ ν}
  {start leftCount rightCount : Nat} :
-- imply
  (sortSliceRangeEntries slice start (leftCount + rightCount)).toList = (sortSliceRangeEntries slice start leftCount).toList ++ (sortSliceRangeEntries slice (start + leftCount) rightCount).toList := by
-- proof
  simp only [sortSliceRangeEntries_toList, List.take_add, List.drop_drop]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeEntries_toList_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeEntries_toList_drop
  {slice : SortSlice κ ν}
  {start count skipped : Nat} :
-- imply
  (sortSliceRangeEntries slice start count).toList.drop skipped = (sortSliceRangeEntries slice (start + skipped) (count - skipped)).toList := by
-- proof
  rw [sortSliceRangeEntries_toList, sortSliceRangeEntries_toList]
  simp [List.drop_take, List.drop_drop]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeKeys_toList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeKeys_toList
  {slice : SortSlice κ ν}
  {start count : Nat} :
-- imply
  (sortSliceRangeKeys slice start count).toList = ((slice.entries.toList.drop start).take count).map SortSliceEntry.key := by
-- proof
  simp [sortSliceRangeKeys, sortSliceRangeEntries_toList]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeKeys_toList_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeKeys_toList_drop
  {slice : SortSlice κ ν}
  {start count skipped : Nat} :
-- imply
  (sortSliceRangeKeys slice start count).toList.drop skipped = (sortSliceRangeKeys slice (start + skipped) (count - skipped)).toList := by
-- proof
  rw [sortSliceRangeKeys_toList, sortSliceRangeKeys_toList]
  simp [List.drop_take, List.drop_drop]

end CPythonListsort

namespace CPythonListsort.SortSlice

/--
[read?_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma read?_ofNat (slice : SortSlice κ ν) (index : Nat) :
  slice.read? (Int.ofNat index) = slice.entries[index]? := by
  simp [read?]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice.EqualOutsideRange

/--
[size_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma size_eq
  {before after : SortSlice κ ν}
  {start count : Nat}
-- given
  (h : EqualOutsideRange before after start count) :
-- imply
  before.entries.size = after.entries.size :=
-- proof
  h.1

end CPythonListsort.SortSlice.EqualOutsideRange

namespace CPythonListsort.SortSlice.EqualOutsideRange

/--
[entries_eq_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma entries_eq_of_disjoint
  {before after : SortSlice κ ν}
  {start count : Nat}
  {otherStart otherCount : Nat}
-- given
  (h : EqualOutsideRange before after start count)
  (hdisjoint : otherStart + otherCount ≤ start ∨ start + count ≤ otherStart) :
-- imply
  sortSliceRangeEntries before otherStart otherCount = sortSliceRangeEntries after otherStart otherCount :=
-- proof
  h.2 otherStart otherCount hdisjoint

end CPythonListsort.SortSlice.EqualOutsideRange

namespace CPythonListsort.SortSlice.EqualOutsideRange

/--
[keys_eq_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma keys_eq_of_disjoint
  {before after : SortSlice κ ν}
  {start count : Nat}
  {otherStart otherCount : Nat}
-- given
  (h : EqualOutsideRange before after start count)
  (hdisjoint : otherStart + otherCount ≤ start ∨ start + count ≤ otherStart) :
-- imply
  sortSliceRangeKeys before otherStart otherCount = sortSliceRangeKeys after otherStart otherCount := by
-- proof
  simp only [sortSliceRangeKeys]
  rw [h.entries_eq_of_disjoint otherStart otherCount hdisjoint]

end CPythonListsort.SortSlice.EqualOutsideRange

namespace CPythonListsort.SortSlice.EqualOutsideRange

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma refl
  {slice : SortSlice κ ν}
  {start count : Nat} :
-- imply
  EqualOutsideRange slice slice start count :=
-- proof
⟨rfl, fun _ _ _ => rfl⟩

end CPythonListsort.SortSlice.EqualOutsideRange

namespace CPythonListsort.SortSlice.EqualOutsideRange

/--
[symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma symm
  {before after : SortSlice κ ν}
  {start count : Nat}
-- given
  (h : EqualOutsideRange before after start count) :
-- imply
  EqualOutsideRange after before start count := by
-- proof
  refine ⟨h.size_eq.symm, ?_⟩
  intro otherStart otherCount hdisjoint
  exact (h.entries_eq_of_disjoint otherStart otherCount hdisjoint).symm

end CPythonListsort.SortSlice.EqualOutsideRange

namespace CPythonListsort.SortSlice.EqualOutsideRange

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma trans
  {first second third : SortSlice κ ν}
  {start count : Nat}
-- given
  (h₁ : EqualOutsideRange first second start count)
  (h₂ : EqualOutsideRange second third start count) :
-- imply
  EqualOutsideRange first third start count := by
-- proof
  refine ⟨h₁.size_eq.trans h₂.size_eq, ?_⟩
  intro otherStart otherCount hdisjoint
  exact (h₁.entries_eq_of_disjoint otherStart otherCount hdisjoint).trans
    (h₂.entries_eq_of_disjoint otherStart otherCount hdisjoint)

end CPythonListsort.SortSlice.EqualOutsideRange

namespace CPythonListsort.SortSlice.EqualOutsideRange

/--
[widen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma widen
  {before after : SortSlice κ ν}
  {smallStart smallCount bigStart bigCount : Nat}
-- given
  (h : EqualOutsideRange before after smallStart smallCount)
  (hstart : bigStart ≤ smallStart)
  (hstop : smallStart + smallCount ≤ bigStart + bigCount) :
-- imply
  EqualOutsideRange before after bigStart bigCount := by
-- proof
  refine ⟨h.size_eq, ?_⟩
  intro otherStart otherCount hdisjoint
  apply h.entries_eq_of_disjoint otherStart otherCount
  obtain hbefore | hafter := hdisjoint
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end CPythonListsort.SortSlice.EqualOutsideRange

namespace CPythonListsort.SortSlice.EqualOutsideRange

/--
[of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma of_eq
  {before after : SortSlice κ ν}
  {start count : Nat}
-- given
  (h : before = after) :
-- imply
  EqualOutsideRange before after start count := by
-- proof
  subst after
  exact refl before start count

end CPythonListsort.SortSlice.EqualOutsideRange

namespace CPythonListsort

/--
[sortSliceRangeEntries_toList_eq_of_reads](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
lemma sortSliceRangeEntries_toList_eq_of_reads
  {slice : SortSlice κ ν}
  {start count : Nat}
  {entries : List (SortSliceEntry κ ν)}
-- given
  (hstop : start + count ≤ slice.entries.size)
  (hlength : entries.length = count)
  (hread : ∀ offset, offset < count → slice.read? (Int.ofNat (start + offset)) = entries[offset]?) :
-- imply
  (sortSliceRangeEntries slice start count).toList = entries := by
-- proof
  apply List.ext_getElem?
  intro offset
  by_cases hoffset : offset < count
  · have h := hread offset hoffset
    rw [SortSlice.read?_ofNat] at h
    rw [sortSliceRangeEntries_toList]
    simpa [hoffset, hstop] using h
  · rw [List.getElem?_eq_none (by
    rw [show (sortSliceRangeEntries slice start count).toList.length =
      count by simp [sortSliceRangeEntries_size _ _ _ hstop]]
    omega),
    List.getElem?_eq_none (by omega)]

end CPythonListsort

/--
[read](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean)
-/
@[path]
private lemma read_eq
  {slice : SortSlice κ ν}
  {index : Nat} :
-- imply
  slice.read? (Int.ofNat index) = slice.entries[index]? := by
-- proof
  apply CPythonListsort.SortSlice.read slice index


-- created on 2026-10-23
