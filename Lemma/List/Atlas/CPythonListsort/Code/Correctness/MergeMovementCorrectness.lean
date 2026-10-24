import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Correctness.MergeMovementCorrectness
open CPythonListsort CPythonListsort.SortSlice


namespace CPythonListsort.SortSlice

/--
[write_eq_some_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma write_eq_some_spec
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {index : Int}
  {entry : SortSliceEntry kappa nu}
-- given
  (hwrite : slice.write? index entry = some updated) :
-- imply
  0 ≤ index ∧ ∃ hinBounds : index.toNat < slice.entries.size, updated = { entries := slice.entries.set index.toNat entry hinBounds } := by
-- proof
  unfold write? at hwrite
  split at hwrite
  · rename_i hnonnegative
    dsimp only at hwrite
    split at hwrite
    · rename_i hinBounds
      injection hwrite with hwrite
      exact ⟨hnonnegative, hinBounds, hwrite.symm⟩
    · simp at hwrite
  · simp at hwrite

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[write_read_self_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma write_read_self_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {index : Int}
  {entry : SortSliceEntry kappa nu}
-- given
  (hwrite : slice.write? index entry = some updated) :
-- imply
  updated.read? index = some entry := by
-- proof
  rcases write_eq_some_spec slice updated index entry hwrite with
    ⟨hnonnegative, hinBounds, rfl⟩
  simp [read?, hnonnegative, hinBounds]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[write_read_ne_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma write_read_ne_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {written index : Int}
  {entry : SortSliceEntry kappa nu}
-- given
  (hwrite : slice.write? written entry = some updated)
  (hne : index ≠ written) :
-- imply
  updated.read? index = slice.read? index := by
-- proof
  rcases write_eq_some_spec slice updated written entry hwrite with
    ⟨hwritten, hinBounds, rfl⟩
  by_cases hindex : 0 ≤ index
  · have hnatne : written.toNat ≠ index.toNat := by
    intro heq
    apply hne
    have hwrittenCast := Int.toNat_of_nonneg hwritten
    have hindexCast := Int.toNat_of_nonneg hindex
    omega
    simp [read?, hindex, Array.getElem?_set_ne _ hnatne]
  · simp [read?, hindex]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[write_readFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma write_readFrame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {index : Int}
  {entry : SortSliceEntry kappa nu}
-- given
  (hwrite : slice.write? index entry = some updated) :
-- imply
  ReadFrame slice updated index 1 := by
-- proof
  refine ⟨(write_entries_size_of_eq_some slice updated index entry hwrite).symm, ?_⟩
  intro other houtside
  apply write_read_ne_of_eq_some slice updated index other entry hwrite
  intro heq
  subst other
  obtain hbefore | hafter <;> simp at * := houtside

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copy_read_destination_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma copy_read_destination_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {dst src : Int}
-- given
  (hcopy : slice.copy? dst src = some updated) :
-- imply
  updated.read? dst = slice.read? src := by
-- proof
  simp only [copy?, copyFrom?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i entry hread
    exact (write_read_self_of_eq_some slice updated dst entry hcopy).trans hread.symm

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copy_read_ne_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma copy_read_ne_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {dst src index : Int}
-- given
  (hcopy : slice.copy? dst src = some updated)
  (hne : index ≠ dst) :
-- imply
  updated.read? index = slice.read? index := by
-- proof
  simp only [copy?, copyFrom?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i entry hread
    exact write_read_ne_of_eq_some slice updated dst index entry hcopy hne

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copy_readFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma copy_readFrame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {dst src : Int}
-- given
  (hcopy : slice.copy? dst src = some updated) :
-- imply
  ReadFrame slice updated dst 1 := by
-- proof
  refine ⟨(copy_entries_size_of_eq_some slice updated dst src hcopy).symm, ?_⟩
  intro index houtside
  apply copy_read_ne_of_eq_some slice updated dst src index hcopy
  intro heq
  subst index
  obtain hbefore | hafter <;> simp at * := houtside

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[ReadFrame.equalOutsideRange_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma ReadFrame.equalOutsideRange_ofNat
  {kappa : Type u}
  {nu : Type v}
  {before after : SortSlice kappa nu}
  {start count : Nat}
-- given
  (hframe : ReadFrame before after (Int.ofNat start) count) :
-- imply
  EqualOutsideRange before after start count := by
-- proof
  refine ⟨hframe.1, ?_⟩
  intro otherStart otherCount hdisjoint
  apply Array.ext_getElem?
  intro offset
  simp only [sortSliceRangeEntries, Array.getElem?_extract]
  rw [← hframe.1]
  by_cases hoffset :
    offset < min (otherStart + otherCount) before.entries.size - otherStart
  · rw [if_pos hoffset, if_pos hoffset]
    have hindexOutside :
      Int.ofNat (otherStart + offset) < Int.ofNat start ∨
        Int.ofNat start + Int.ofNat count ≤
          Int.ofNat (otherStart + offset) := by
      obtain hbefore | hafter := hdisjoint
      · left
        exact Int.ofNat_lt.mpr (by omega)
      · right
        simp only [Int.ofNat_eq_natCast]
        omega
    have hread := hframe.2 (Int.ofNat (otherStart + offset)) hindexOutside
    simpa only [read?_ofNat] using hread.symm
  · rw [if_neg hoffset, if_neg hoffset]

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[write_equalOutsideRange_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma write_equalOutsideRange_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {index : Int}
  {entry : SortSliceEntry kappa nu}
-- given
  (hwrite : slice.write? index entry = some updated) :
-- imply
  EqualOutsideRange slice updated index.toNat 1 := by
-- proof
  have hindex := (write_eq_some_spec slice updated index entry hwrite).1
  have hcast : Int.ofNat index.toNat = index := Int.toNat_of_nonneg hindex
  have hframe := write_readFrame_of_eq_some slice updated index entry hwrite
  rwa [← hcast] at hframe

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

variable {kappa : Type u} {nu : Type v}
/--
[copy_dst_nonnegative_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma copy_dst_nonnegative_of_eq_some
  (slice updated : SortSlice kappa nu) (dst src : Int)
  (hcopy : slice.copy? dst src = some updated) : 0 ≤ dst := by
  simp only [copy?, copyFrom?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i entry hread
    exact (write_eq_some_spec slice updated dst entry hcopy).1

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[copy_equalOutsideRange_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma copy_equalOutsideRange_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {dst src : Int}
-- given
  (hcopy : slice.copy? dst src = some updated) :
-- imply
  EqualOutsideRange slice updated dst.toNat 1 := by
-- proof
  have hdst := copy_dst_nonnegative_of_eq_some slice updated dst src hcopy
  have hcast : Int.ofNat dst.toNat = dst := Int.toNat_of_nonneg hdst
  have hframe := copy_readFrame_of_eq_some slice updated dst src hcopy
  rwa [← hcast] at hframe

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

variable {kappa : Type u} {nu : Type v}
/--
[memmoveForward_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma memmoveForward_correct
  (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
  (hdirection : dst ≤ src)
  (hresult : memmoveForward? count slice dst src = some updated) :
  CopiesRange slice updated dst src count ∧
    ReadFrame slice updated dst count := by
  induction count generalizing slice updated dst src with
  | zero =>
    simp only [memmoveForward?] at hresult
    injection hresult with hresult
    subst updated
    refine ⟨?_, ⟨rfl, ?_⟩⟩
    · intro i hi
      omega
    · intro index _houtside
      rfl
  | succ count ih =>
    rw [memmoveForward?] at hresult
    rcases Option.bind_eq_some_iff.mp hresult with
      ⟨afterHead, hhead, htail⟩
    rcases ih afterHead updated (dst + 1) (src + 1) (by omega) htail with
      ⟨htailCopy, htailFrame⟩
    have hheadFrame := copy_readFrame_of_eq_some slice afterHead dst src hhead
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        have hpreserved := htailFrame.2 dst (Or.inl (by omega))
        have hcopied := copy_read_destination_of_eq_some
          slice afterHead dst src hhead
        simpa using hpreserved.trans hcopied
      | succ i =>
        have hiTail : i < count := by omega
        have hcopied := htailCopy i hiTail
        have hpreserved := copy_read_ne_of_eq_some slice afterHead dst src
          (src + 1 + Int.ofNat i) hhead (by
            simp only [Int.ofNat_eq_natCast]
            omega)
        calc
          updated.read? (dst + Int.ofNat (Nat.succ i)) =
            updated.read? (dst + 1 + Int.ofNat i) := by
              congr 1
              simp only [Int.ofNat_eq_natCast]
              omega
          _ = afterHead.read? (src + 1 + Int.ofNat i) := hcopied
          _ = slice.read? (src + 1 + Int.ofNat i) := hpreserved
          _ = slice.read? (src + Int.ofNat (Nat.succ i)) := by
            congr 1
            simp only [Int.ofNat_eq_natCast]
            omega
    · refine ⟨hheadFrame.1.trans htailFrame.1, ?_⟩
      intro index houtside
      have htailOutside :
        index < dst + 1 ∨
          (dst + 1) + Int.ofNat count ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl (by omega)
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl hbefore
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      exact (htailFrame.2 index htailOutside).trans
        (hheadFrame.2 index hheadOutside)

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

variable {kappa : Type u} {nu : Type v}
/--
[memmoveBackward_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma memmoveBackward_correct
  (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
  (hdirection : src < dst)
  (hresult : memmoveBackward? count slice dst src = some updated) :
  CopiesRange slice updated dst src count ∧
    ReadFrame slice updated dst count := by
  induction count generalizing slice updated with
  | zero =>
    simp only [memmoveBackward?] at hresult
    injection hresult with hresult
    subst updated
    refine ⟨?_, ⟨rfl, ?_⟩⟩
    · intro i hi
      omega
    · intro index _houtside
      rfl
  | succ count ih =>
    rw [memmoveBackward?] at hresult
    rcases Option.bind_eq_some_iff.mp hresult with
      ⟨afterHead, hhead, htail⟩
    obtain ⟨htailCopy, htailFrame⟩ := ih afterHead updated htail
    have hheadFrame := copy_readFrame_of_eq_some slice afterHead
      (dst + Int.ofNat count) (src + Int.ofNat count) hhead
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases hilast : i = count
      · subst i
        have hpreserved := htailFrame.2 (dst + Int.ofNat count)
          (Or.inr le_rfl)
        have hcopied := copy_read_destination_of_eq_some slice afterHead
          (dst + Int.ofNat count) (src + Int.ofNat count) hhead
        exact hpreserved.trans hcopied
      · have hiTail : i < count := by omega
        have hcopied := htailCopy i hiTail
        have hpreserved := copy_read_ne_of_eq_some slice afterHead
          (dst + Int.ofNat count) (src + Int.ofNat count)
          (src + Int.ofNat i) hhead (by
            simp only [Int.ofNat_eq_natCast]
            omega)
        exact hcopied.trans hpreserved
    · refine ⟨hheadFrame.1.trans htailFrame.1, ?_⟩
      intro index houtside
      have htailOutside :
        index < dst ∨ dst + Int.ofNat count ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl hbefore
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      have hheadOutside :
        index < dst + Int.ofNat count ∨
          dst + Int.ofNat count + 1 ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl (by
          simp only [Int.ofNat_eq_natCast]
          omega)
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      exact (htailFrame.2 index htailOutside).trans
        (hheadFrame.2 index hheadOutside)

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmove_copiesRange_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma memmove_copiesRange_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {dst src : Int}
  {count : Nat}
-- given
  (hresult : slice.memmove? dst src count = some updated) :
-- imply
  CopiesRange slice updated dst src count := by
-- proof
  by_cases hdirection : dst ≤ src
  · rw [memmove?, memmoveDirection, if_pos hdirection] at hresult
    exact (memmoveForward_correct count slice updated dst src hdirection hresult).1
  · rw [memmove?, memmoveDirection, if_neg hdirection] at hresult
    exact (memmoveBackward_correct count slice updated dst src
      (lt_of_not_ge hdirection) hresult).1

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmove_readFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma memmove_readFrame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {dst src : Int}
  {count : Nat}
-- given
  (hresult : slice.memmove? dst src count = some updated) :
-- imply
  ReadFrame slice updated dst count := by
-- proof
  by_cases hdirection : dst ≤ src
  · rw [memmove?, memmoveDirection, if_pos hdirection] at hresult
    exact (memmoveForward_correct count slice updated dst src hdirection hresult).2
  · rw [memmove?, memmoveDirection, if_neg hdirection] at hresult
    exact (memmoveBackward_correct count slice updated dst src
      (lt_of_not_ge hdirection) hresult).2

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

variable {kappa : Type u} {nu : Type v}
/--
[memmoveForward_dst_nonnegative_of_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma memmoveForward_dst_nonnegative_of_success
  (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
  (hcount : 0 < count)
  (hresult : memmoveForward? count slice dst src = some updated) :
  0 ≤ dst := by
  cases count with
  | zero => omega
  | succ count =>
    rw [memmoveForward?] at hresult
    obtain ⟨afterHead, hhead, _htail⟩ := Option.bind_eq_some_iff.mp hresult
    exact copy_dst_nonnegative_of_eq_some slice afterHead dst src hhead

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

variable {kappa : Type u} {nu : Type v}
/--
[memmoveBackward_dst_nonnegative_of_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma memmoveBackward_dst_nonnegative_of_success
  (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
  (hcount : 0 < count)
  (hresult : memmoveBackward? count slice dst src = some updated) :
  0 ≤ dst := by
  induction count generalizing slice updated with
  | zero => omega
  | succ count ih =>
    rw [memmoveBackward?] at hresult
    rcases Option.bind_eq_some_iff.mp hresult with
      ⟨afterHead, hhead, htail⟩
    cases count with
    | zero =>
      have hhead' : slice.copy? dst src = some afterHead := by
        simpa using hhead
      exact copy_dst_nonnegative_of_eq_some slice afterHead dst src hhead'
    | succ count =>
      exact ih afterHead updated (by omega) htail

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

variable {kappa : Type u} {nu : Type v}
/--
[memmove_dst_nonnegative_of_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma memmove_dst_nonnegative_of_success
  (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
  (hcount : 0 < count)
  (hresult : slice.memmove? dst src count = some updated) :
  0 ≤ dst := by
  by_cases hdirection : dst ≤ src
  · rw [memmove?, memmoveDirection, if_pos hdirection] at hresult
    exact memmoveForward_dst_nonnegative_of_success count slice updated dst src
      hcount hresult
  · rw [memmove?, memmoveDirection, if_neg hdirection] at hresult
    exact memmoveBackward_dst_nonnegative_of_success count slice updated dst src
      hcount hresult

end CPythonListsort.SortSlice

namespace CPythonListsort.SortSlice

/--
[memmove_equalOutsideRange_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma memmove_equalOutsideRange_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {slice updated : SortSlice kappa nu}
  {dst src : Int}
  {count : Nat}
-- given
  (hresult : slice.memmove? dst src count = some updated) :
-- imply
  EqualOutsideRange slice updated dst.toNat count := by
-- proof
  by_cases hcount : count = 0
  · subst count
    have hsame : updated = slice := by
      by_cases hdirection : dst ≤ src
      · rw [memmove?, memmoveDirection, if_pos hdirection] at hresult
        simpa [memmoveForward?] using hresult.symm
      · rw [memmove?, memmoveDirection, if_neg hdirection] at hresult
        simpa [memmoveBackward?] using hresult.symm
    subst updated
    exact EqualOutsideRange.refl slice dst.toNat 0
  · have hdst := memmove_dst_nonnegative_of_success count slice updated dst src
    (Nat.pos_of_ne_zero hcount) hresult
    have hcast : Int.ofNat dst.toNat = dst := Int.toNat_of_nonneg hdst
    have hframe := memmove_readFrame_of_eq_some slice updated dst src count hresult
    rwa [← hcast] at hframe

end CPythonListsort.SortSlice

namespace CPythonListsort

/--
[mergeLoTempWrite_readFrameNat_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoTempWrite_readFrameNat_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {storage updated : TempStorage kappa nu}
  {dst : Nat}
  {entry : SortSliceEntry kappa nu}
-- given
  (hwrite : mergeLoTempWrite? storage dst entry = some updated) :
-- imply
  TempStorage.ReadFrameNat storage updated dst 1 := by
-- proof
  simp only [mergeLoTempWrite?] at hwrite
  split at hwrite
  · injection hwrite with hwrite
    subst updated
    refine
      { cellsSize := by simp
        backing := rfl
        hasValues := rfl
        read_eq := ?_ }
    intro index houtside
    apply mergeLoTempRead_write_ne_of_eq_some storage
      { storage with cells := storage.cells.set dst (some entry) }
      dst index entry (by simp [mergeLoTempWrite?, *])
    intro heq
    subst index
    obtain hbefore | hafter <;> omega := houtside
  · simp at hwrite

end CPythonListsort

namespace CPythonListsort

variable {kappa : Type u} {nu : Type v}
/--
[mergeLoMemcpyDataToTemp_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma mergeLoMemcpyDataToTemp_spec
  (site : MergeLoMemcpyCallsite)
  (hDirection : site.backings =
    { destination := .temporary, source := .main })
  (count : Nat) (state state' : MergeState kappa nu)
  (dst : Nat) (src : Int)
  (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src =
    some state') :
  state'.data = state.data ∧
    (∀ i, i < count →
      mergeLoTempRead? state'.a (dst + i) =
        state.data.read? (src + Int.ofNat i)) ∧
    TempStorage.ReadFrameNat state.a state'.a dst count := by
  induction count generalizing state state' dst src with
  | zero =>
    simp only [mergeLoMemcpyDataToTemp?] at hcopy
    injection hcopy with hcopy
    subst state'
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      omega
    · exact
      { cellsSize := rfl
        backing := rfl
        hasValues := rfl
        read_eq := fun _ _ => rfl }
  | succ count ih =>
    rw [mergeLoMemcpyDataToTemp?] at hcopy
    obtain ⟨entry, hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
    obtain ⟨storage, hwrite, htail⟩ := Option.bind_eq_some_iff.mp hcopy
    obtain a := storage } state' (dst + 1) (src + 1) htail with := ih { state
      ⟨hdata, htailCopy, htailFrame⟩
    have hheadFrame :=
      mergeLoTempWrite_readFrameNat_of_eq_some state.a storage dst entry hwrite
    refine ⟨hdata, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        have hpreserved := htailFrame.read_eq dst (Or.inl (by omega))
        have hwritten := mergeLoTempRead_write_self_of_eq_some
          state.a storage dst entry hwrite
        simpa using hpreserved.trans (hwritten.trans hread.symm)
      | succ i =>
        have hiTail : i < count := by omega
        have hcopied := htailCopy i hiTail
        calc
          mergeLoTempRead? state'.a (dst + Nat.succ i) =
            state.data.read? (src + 1 + Int.ofNat i) := by
              simpa only [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hcopied
          _ = state.data.read? (src + Int.ofNat (Nat.succ i)) := by
            congr 1
            simp only [Int.ofNat_eq_natCast]
            omega
    · refine
      { cellsSize := hheadFrame.cellsSize.trans htailFrame.cellsSize
        backing := hheadFrame.backing.trans htailFrame.backing
        hasValues := hheadFrame.hasValues.trans htailFrame.hasValues
        read_eq := ?_ }
      intro index houtside
      have htailOutside :
        index < dst + 1 ∨ dst + 1 + count ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl hbefore
        · exact Or.inr (by omega)
      exact (htailFrame.read_eq index htailOutside).trans
        (hheadFrame.read_eq index hheadOutside)

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyDataToTemp_data_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoMemcpyDataToTemp_data_eq_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst : Nat}
  {src : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src = some state') :
-- imply
  state'.data = state.data :=
-- proof
  (mergeLoMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).1

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyDataToTemp_read_range_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoMemcpyDataToTemp_read_range_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst : Nat}
  {src : Int}
  {i : Nat}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src = some state')
  (hi : i < count) :
-- imply
  mergeLoTempRead? state'.a (dst + i) = state.data.read? (src + Int.ofNat i) :=
-- proof
  (mergeLoMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).2.1 i hi

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyDataToTemp_tempFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoMemcpyDataToTemp_tempFrame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst : Nat}
  {src : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src = some state') :
-- imply
  TempStorage.ReadFrameNat state.a state'.a dst count :=
-- proof
  (mergeLoMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).2.2

end CPythonListsort

namespace CPythonListsort

variable {kappa : Type u} {nu : Type v}
/--
[mergeLoMemcpyTempToData_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma mergeLoMemcpyTempToData_spec
  (site : MergeLoMemcpyCallsite)
  (hDirection : site.backings =
    { destination := .main, source := .temporary })
  (count : Nat) (state state' : MergeState kappa nu)
  (dst : Int) (src : Nat)
  (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src =
    some state') :
  state'.a = state.a ∧
    (∀ i, i < count →
      state'.data.read? (dst + Int.ofNat i) =
        mergeLoTempRead? state.a (src + i)) ∧
    SortSlice.ReadFrame state.data state'.data dst count := by
  induction count generalizing state state' dst src with
  | zero =>
    simp only [mergeLoMemcpyTempToData?] at hcopy
    injection hcopy with hcopy
    subst state'
    refine ⟨rfl, ?_, ⟨rfl, ?_⟩⟩
    · intro i hi
      omega
    · intro index _houtside
      rfl
  | succ count ih =>
    rw [mergeLoMemcpyTempToData?] at hcopy
    obtain ⟨entry, hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
    obtain ⟨data, hwrite, htail⟩ := Option.bind_eq_some_iff.mp hcopy
    obtain data := data } state' (dst + 1) (src + 1) htail with := ih { state
      ⟨htemp, htailCopy, htailFrame⟩
    have hheadFrame := SortSlice.write_readFrame_of_eq_some
      state.data data dst entry hwrite
    refine ⟨htemp, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        have hpreserved := htailFrame.2 dst (Or.inl (by omega))
        have hwritten := SortSlice.write_read_self_of_eq_some
          state.data data dst entry hwrite
        simpa using hpreserved.trans (hwritten.trans hread.symm)
      | succ i =>
        have hiTail : i < count := by omega
        have hcopied := htailCopy i hiTail
        calc
          state'.data.read? (dst + Int.ofNat (Nat.succ i)) =
            state'.data.read? (dst + 1 + Int.ofNat i) := by
              congr 1
              simp only [Int.ofNat_eq_natCast]
              omega
          _ = mergeLoTempRead? state.a (src + Nat.succ i) := by
            simpa only [Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hcopied
    · refine ⟨hheadFrame.1.trans htailFrame.1, ?_⟩
      intro index houtside
      have htailOutside :
        index < dst + 1 ∨ (dst + 1) + Int.ofNat count ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl (by omega)
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl hbefore
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      exact (htailFrame.2 index htailOutside).trans
        (hheadFrame.2 index hheadOutside)

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyTempToData_temp_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoMemcpyTempToData_temp_eq_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst : Int}
  {src : Nat}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src = some state') :
-- imply
  state'.a = state.a :=
-- proof
  (mergeLoMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).1

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyTempToData_read_range_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoMemcpyTempToData_read_range_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst : Int}
  {src : Nat}
  {i : Nat}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src = some state')
  (hi : i < count) :
-- imply
  state'.data.read? (dst + Int.ofNat i) = mergeLoTempRead? state.a (src + i) :=
-- proof
  (mergeLoMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).2.1 i hi

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyTempToData_readFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoMemcpyTempToData_readFrame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst : Int}
  {src : Nat}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src = some state') :
-- imply
  SortSlice.ReadFrame state.data state'.data dst count :=
-- proof
  (mergeLoMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).2.2

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyTempToData_equalOutsideRange_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoMemcpyTempToData_equalOutsideRange_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst : Int}
  {src : Nat}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src = some state') :
-- imply
  SortSlice.EqualOutsideRange state.data state'.data dst.toNat count := by
-- proof
  cases count with
  | zero =>
    simp only [mergeLoMemcpyTempToData?] at hcopy
    injection hcopy with hcopy
    subst state'
    exact SortSlice.EqualOutsideRange.refl state.data dst.toNat 0
  | succ count =>
    have hcopyHead := hcopy
    rw [mergeLoMemcpyTempToData?] at hcopyHead
    obtain ⟨entry, _hread, hcopyHead⟩ := Option.bind_eq_some_iff.mp hcopyHead
    obtain ⟨data, hwrite, _htail⟩ := Option.bind_eq_some_iff.mp hcopyHead
    have hdst := (SortSlice.write_eq_some_spec state.data data dst entry hwrite).1
    have hcast : Int.ofNat dst.toNat = dst := Int.toNat_of_nonneg hdst
    have hframe := mergeLoMemcpyTempToData_readFrame_of_eq_some site hDirection
      (count + 1) state state' dst src hcopy
    rwa [← hcast] at hframe

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiTempWrite_readFrameInt_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiTempWrite_readFrameInt_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {storage updated : TempStorage kappa nu}
  {dst : Int}
  {entry : SortSliceEntry kappa nu}
-- given
  (hwrite : mergeHiTempWrite? storage dst entry = some updated) :
-- imply
  TempStorage.ReadFrameInt storage updated dst 1 := by
-- proof
  unfold mergeHiTempWrite? at hwrite
  split at hwrite
  · rename_i hdst
    dsimp only at hwrite
    split at hwrite
    · rename_i hbound
      injection hwrite with hwrite
      subst updated
      refine
        { cellsSize := by simp
          backing := rfl
          hasValues := rfl
          read_eq := ?_ }
      intro index houtside
      apply mergeHiTempWrite_read_of_ne storage
        { storage with cells := storage.cells.set dst.toNat (some entry) }
        dst index entry (by simp [mergeHiTempWrite?, hdst, hbound])
      intro heq
      subst index
      obtain hbefore | hafter <;> simp at * := houtside
    · simp at hwrite
  · simp at hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyDataToTemp_data_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiCopyDataToTemp_data_eq_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {state state' : MergeState kappa nu}
  {dst src : Int}
-- given
  (hcopy : mergeHiCopyDataToTemp? state dst src = some state') :
-- imply
  state'.data = state.data := by
-- proof
  obtain ⟨entry, _hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨storage, _hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hfinal with hfinal
  subst state'
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyDataToTemp_tempFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiCopyDataToTemp_tempFrame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {state state' : MergeState kappa nu}
  {dst src : Int}
-- given
  (hcopy : mergeHiCopyDataToTemp? state dst src = some state') :
-- imply
  TempStorage.ReadFrameInt state.a state'.a dst 1 := by
-- proof
  obtain ⟨entry, _hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨storage, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hfinal with hfinal
  subst state'
  exact mergeHiTempWrite_readFrameInt_of_eq_some state.a storage dst entry hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyTempToData_read_destination_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiCopyTempToData_read_destination_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {state state' : MergeState kappa nu}
  {dst src : Int}
-- given
  (hcopy : mergeHiCopyTempToData? state dst src = some state') :
-- imply
  state'.data.read? dst = mergeHiTempRead? state.a src := by
-- proof
  obtain ⟨entry, hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨data, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hfinal with hfinal
  subst state'
  exact (SortSlice.write_read_self_of_eq_some state.data data dst entry
    hwrite).trans hread.symm

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyTempToData_read_ne_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiCopyTempToData_read_ne_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {state state' : MergeState kappa nu}
  {dst src index : Int}
-- given
  (hcopy : mergeHiCopyTempToData? state dst src = some state')
  (hne : index ≠ dst) :
-- imply
  state'.data.read? index = state.data.read? index := by
-- proof
  obtain ⟨entry, _hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨data, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hfinal with hfinal
  subst state'
  exact SortSlice.write_read_ne_of_eq_some state.data data dst index entry
    hwrite hne

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyTempToData_frame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiCopyTempToData_frame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {state state' : MergeState kappa nu}
  {dst src : Int}
-- given
  (hcopy : mergeHiCopyTempToData? state dst src = some state') :
-- imply
  state'.a = state.a ∧ SortSlice.ReadFrame state.data state'.data dst 1 := by
-- proof
  obtain ⟨entry, _hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨data, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hfinal with hfinal
  subst state'
  exact ⟨rfl, SortSlice.write_readFrame_of_eq_some state.data data dst entry
    hwrite⟩

end CPythonListsort

namespace CPythonListsort

variable {kappa : Type u} {nu : Type v}
/--
[mergeHiMemcpyDataToTemp_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma mergeHiMemcpyDataToTemp_spec
  (site : MergeHiMemcpyCallsite)
  (hDirection : site.backings =
    { destination := .temporary, source := .main })
  (count : Nat) (state state' : MergeState kappa nu)
  (dst src : Int)
  (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
    some state') :
  state'.data = state.data ∧
    (∀ i, i < count →
      mergeHiTempRead? state'.a (dst + Int.ofNat i) =
        state.data.read? (src + Int.ofNat i)) ∧
    TempStorage.ReadFrameInt state.a state'.a dst count := by
  induction count generalizing state state' dst src with
  | zero =>
    simp only [mergeHiMemcpyDataToTemp?] at hcopy
    injection hcopy with hcopy
    subst state'
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      omega
    · exact
      { cellsSize := rfl
        backing := rfl
        hasValues := rfl
        read_eq := fun _ _ => rfl }
  | succ count ih =>
    rw [mergeHiMemcpyDataToTemp?] at hcopy
    obtain ⟨afterHead, hhead, htail⟩ := Option.bind_eq_some_iff.mp hcopy
    rcases ih afterHead state' (dst + 1) (src + 1) htail with
      ⟨hdataTail, htailCopy, htailFrame⟩
    have hdataHead :=
      mergeHiCopyDataToTemp_data_eq_of_eq_some state afterHead dst src hhead
    have hheadFrame :=
      mergeHiCopyDataToTemp_tempFrame_of_eq_some state afterHead dst src hhead
    refine ⟨hdataTail.trans hdataHead, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        have hpreserved := htailFrame.read_eq dst (Or.inl (by omega))
        rcases mergeHiCopyDataToTemp_read_eq_some state afterHead dst src
          hhead with ⟨entry, hsource, hwritten⟩
        simpa using hpreserved.trans (hwritten.trans hsource.symm)
      | succ i =>
        have hiTail : i < count := by omega
        have hcopied := htailCopy i hiTail
        calc
          mergeHiTempRead? state'.a (dst + Int.ofNat (Nat.succ i)) =
            mergeHiTempRead? state'.a (dst + 1 + Int.ofNat i) := by
              congr 1
              simp only [Int.ofNat_eq_natCast]
              omega
          _ = afterHead.data.read? (src + 1 + Int.ofNat i) := hcopied
          _ = state.data.read? (src + Int.ofNat (Nat.succ i)) := by
            rw [hdataHead]
            congr 1
            simp only [Int.ofNat_eq_natCast]
            omega
    · refine
      { cellsSize := hheadFrame.cellsSize.trans htailFrame.cellsSize
        backing := hheadFrame.backing.trans htailFrame.backing
        hasValues := hheadFrame.hasValues.trans htailFrame.hasValues
        read_eq := ?_ }
      intro index houtside
      have htailOutside :
        index < dst + 1 ∨ (dst + 1) + Int.ofNat count ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl (by omega)
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl hbefore
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      exact (htailFrame.read_eq index htailOutside).trans
        (hheadFrame.read_eq index hheadOutside)

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyDataToTemp_data_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiMemcpyDataToTemp_data_eq_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src = some state') :
-- imply
  state'.data = state.data :=
-- proof
  (mergeHiMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).1

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyDataToTemp_read_range_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiMemcpyDataToTemp_read_range_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst src : Int}
  {i : Nat}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src = some state')
  (hi : i < count) :
-- imply
  mergeHiTempRead? state'.a (dst + Int.ofNat i) = state.data.read? (src + Int.ofNat i) :=
-- proof
  (mergeHiMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).2.1 i hi

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyDataToTemp_tempFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiMemcpyDataToTemp_tempFrame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src = some state') :
-- imply
  TempStorage.ReadFrameInt state.a state'.a dst count :=
-- proof
  (mergeHiMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).2.2

end CPythonListsort

namespace CPythonListsort

variable {kappa : Type u} {nu : Type v}
/--
[mergeHiMemcpyTempToData_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma mergeHiMemcpyTempToData_spec
  (site : MergeHiMemcpyCallsite)
  (hDirection : site.backings =
    { destination := .main, source := .temporary })
  (count : Nat) (state state' : MergeState kappa nu)
  (dst src : Int)
  (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src =
    some state') :
  state'.a = state.a ∧
    (∀ i, i < count →
      state'.data.read? (dst + Int.ofNat i) =
        mergeHiTempRead? state.a (src + Int.ofNat i)) ∧
    SortSlice.ReadFrame state.data state'.data dst count := by
  induction count generalizing state state' dst src with
  | zero =>
    simp only [mergeHiMemcpyTempToData?] at hcopy
    injection hcopy with hcopy
    subst state'
    refine ⟨rfl, ?_, ⟨rfl, ?_⟩⟩
    · intro i hi
      omega
    · intro index _houtside
      rfl
  | succ count ih =>
    rw [mergeHiMemcpyTempToData?] at hcopy
    obtain ⟨afterHead, hhead, htail⟩ := Option.bind_eq_some_iff.mp hcopy
    rcases ih afterHead state' (dst + 1) (src + 1) htail with
      ⟨htempTail, htailCopy, htailFrame⟩
    rcases mergeHiCopyTempToData_frame_of_eq_some state afterHead dst src
      hhead with ⟨htempHead, hheadFrame⟩
    refine ⟨htempTail.trans htempHead, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        have hpreserved := htailFrame.2 dst (Or.inl (by omega))
        have hwritten := mergeHiCopyTempToData_read_destination_of_eq_some
          state afterHead dst src hhead
        simpa using hpreserved.trans hwritten
      | succ i =>
        have hiTail : i < count := by omega
        have hcopied := htailCopy i hiTail
        calc
          state'.data.read? (dst + Int.ofNat (Nat.succ i)) =
            state'.data.read? (dst + 1 + Int.ofNat i) := by
              congr 1
              simp only [Int.ofNat_eq_natCast]
              omega
          _ = mergeHiTempRead? afterHead.a (src + 1 + Int.ofNat i) :=
            hcopied
          _ = mergeHiTempRead? state.a (src + Int.ofNat (Nat.succ i)) := by
            rw [htempHead]
            congr 1
            simp only [Int.ofNat_eq_natCast]
            omega
    · refine ⟨hheadFrame.1.trans htailFrame.1, ?_⟩
      intro index houtside
      have htailOutside :
        index < dst + 1 ∨ (dst + 1) + Int.ofNat count ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl (by omega)
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
        obtain hbefore | hafter := houtside
        · exact Or.inl hbefore
        · exact Or.inr (by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
          omega)
      exact (htailFrame.2 index htailOutside).trans
        (hheadFrame.2 index hheadOutside)

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyTempToData_temp_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiMemcpyTempToData_temp_eq_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src = some state') :
-- imply
  state'.a = state.a :=
-- proof
  (mergeHiMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).1

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyTempToData_read_range_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiMemcpyTempToData_read_range_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst src : Int}
  {i : Nat}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src = some state')
  (hi : i < count) :
-- imply
  state'.data.read? (dst + Int.ofNat i) = mergeHiTempRead? state.a (src + Int.ofNat i) :=
-- proof
  (mergeHiMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).2.1 i hi

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyTempToData_readFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiMemcpyTempToData_readFrame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src = some state') :
-- imply
  SortSlice.ReadFrame state.data state'.data dst count :=
-- proof
  (mergeHiMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).2.2

end CPythonListsort

namespace CPythonListsort

variable {kappa : Type u} {nu : Type v}
/--
[mergeHiCopyTempToData_dst_nonnegative_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
private lemma mergeHiCopyTempToData_dst_nonnegative_of_eq_some
  (state state' : MergeState kappa nu) (dst src : Int)
  (hcopy : mergeHiCopyTempToData? state dst src = some state') :
  0 ≤ dst := by
  obtain ⟨entry, _hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨data, hwrite, _hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  exact (SortSlice.write_eq_some_spec state.data data dst entry hwrite).1

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyTempToData_equalOutsideRange_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiMemcpyTempToData_equalOutsideRange_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src = some state') :
-- imply
  SortSlice.EqualOutsideRange state.data state'.data dst.toNat count := by
-- proof
  cases count with
  | zero =>
    simp only [mergeHiMemcpyTempToData?] at hcopy
    injection hcopy with hcopy
    subst state'
    exact SortSlice.EqualOutsideRange.refl state.data dst.toNat 0
  | succ count =>
    have hcopyHead := hcopy
    rw [mergeHiMemcpyTempToData?] at hcopyHead
    rcases Option.bind_eq_some_iff.mp hcopyHead with
      ⟨afterHead, hhead, _htail⟩
    have hdst := mergeHiCopyTempToData_dst_nonnegative_of_eq_some
      state afterHead dst src hhead
    have hcast : Int.ofNat dst.toNat = dst := Int.toNat_of_nonneg hdst
    have hframe := mergeHiMemcpyTempToData_readFrame_of_eq_some site hDirection
      (count + 1) state state' dst src hcopy
    rwa [← hcast] at hframe

end CPythonListsort

namespace CPythonListsort

/--
[mergeDataMemmove_copiesRange_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeDataMemmove_copiesRange_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeMemmoveCallsite}
  {data updated : SortSlice kappa nu}
  {dst src : Int}
  {count : Nat}
-- given
  (hmove : mergeDataMemmove? site data dst src count = some updated) :
-- imply
  SortSlice.CopiesRange data updated dst src count :=
-- proof
  SortSlice.memmove_copiesRange_of_eq_some data updated dst src count hmove

end CPythonListsort

namespace CPythonListsort

/--
[mergeDataMemmove_readFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeDataMemmove_readFrame_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeMemmoveCallsite}
  {data updated : SortSlice kappa nu}
  {dst src : Int}
  {count : Nat}
-- given
  (hmove : mergeDataMemmove? site data dst src count = some updated) :
-- imply
  SortSlice.ReadFrame data updated dst count :=
-- proof
  SortSlice.memmove_readFrame_of_eq_some data updated dst src count hmove

end CPythonListsort

namespace CPythonListsort

/--
[mergeDataMemmove_equalOutsideRange_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeDataMemmove_equalOutsideRange_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeMemmoveCallsite}
  {data updated : SortSlice kappa nu}
  {dst src : Int}
  {count : Nat}
-- given
  (hmove : mergeDataMemmove? site data dst src count = some updated) :
-- imply
  SortSlice.EqualOutsideRange data updated dst.toNat count :=
-- proof
  SortSlice.memmove_equalOutsideRange_of_eq_some data updated dst src count hmove

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyDataDecr_spec_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiCopyDataDecr_spec_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {state : MergeState kappa nu}
  {dst src : Int}
  {result : MergeHiDataCursorResult kappa nu}
-- given
  (hcopy : mergeHiCopyDataDecr? state dst src = some result) :
-- imply
  result.dst = dst - 1 ∧ result.src = src - 1 ∧ result.state.a = state.a ∧ result.state.data.read? dst = state.data.read? src ∧ SortSlice.ReadFrame state.data result.state.data dst 1 := by
-- proof
  rw [mergeHiCopyDataDecr?] at hcopy
  obtain ⟨copied, hcopied, hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  rw [SortSlice.copyDecr?, SortSlice.copyFromDecr?] at hcopied
  obtain ⟨data, hsingle, hcursor⟩ := Option.bind_eq_some_iff.mp hcopied
  rw [SortSlice.copyFrom?] at hsingle
  obtain ⟨entry, hread, hwrite⟩ := Option.bind_eq_some_iff.mp hsingle
  injection hcursor with hcursor
  subst copied
  injection hfinal with hfinal
  subst result
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact (SortSlice.write_read_self_of_eq_some state.data data dst entry
    hwrite).trans hread.symm
  · exact SortSlice.write_readFrame_of_eq_some state.data data dst entry hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyTempDecr_spec_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiCopyTempDecr_spec_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {state : MergeState kappa nu}
  {dst src : Int}
  {result : MergeHiDataCursorResult kappa nu}
-- given
  (hcopy : mergeHiCopyTempDecr? state dst src = some result) :
-- imply
  result.dst = dst - 1 ∧ result.src = src - 1 ∧ result.state.a = state.a ∧ result.state.data.read? dst = mergeHiTempRead? state.a src ∧ SortSlice.ReadFrame state.data result.state.data dst 1 := by
-- proof
  rw [mergeHiCopyTempDecr?] at hcopy
  obtain ⟨state', hcell, hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hfinal with hfinal
  subst result
  rcases mergeHiCopyTempToData_frame_of_eq_some state state' dst src hcell with
    ⟨htemp, hframe⟩
  exact ⟨rfl, rfl, htemp,
    mergeHiCopyTempToData_read_destination_of_eq_some state state' dst src hcell,
    hframe⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoCopyAIncr_spec_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoCopyAIncr_spec_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {machine next : MergeLoMachine kappa nu}
-- given
  (hcopy : mergeLoCopyAIncr? machine = some next) :
-- imply
  next.dest = machine.dest + 1 ∧ next.aPos = machine.aPos + 1 ∧ next.bPos = machine.bPos ∧ next.na = machine.na - 1 ∧ next.nb = machine.nb ∧ next.state.key_compare = machine.state.key_compare ∧ next.state.a = machine.state.a ∧ next.state.data.read? machine.dest = mergeLoTempRead? machine.state.a machine.aPos ∧ SortSlice.ReadFrame machine.state.data next.state.data machine.dest 1 := by
-- proof
  rw [mergeLoCopyAIncr?] at hcopy
  obtain ⟨entry, hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨data, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hfinal with hfinal
  subst next
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (SortSlice.write_read_self_of_eq_some machine.state.data data
    machine.dest entry hwrite).trans hread.symm
  · exact SortSlice.write_readFrame_of_eq_some machine.state.data data
    machine.dest entry hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoCopyBIncr_spec_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoCopyBIncr_spec_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {machine next : MergeLoMachine kappa nu}
-- given
  (hcopy : mergeLoCopyBIncr? machine = some next) :
-- imply
  next.dest = machine.dest + 1 ∧ next.aPos = machine.aPos ∧ next.bPos = machine.bPos + 1 ∧ next.na = machine.na ∧ next.nb = machine.nb - 1 ∧ next.state.key_compare = machine.state.key_compare ∧ next.state.a = machine.state.a ∧ next.state.data.read? machine.dest = machine.state.data.read? machine.bPos ∧ SortSlice.ReadFrame machine.state.data next.state.data machine.dest 1 := by
-- proof
  rw [mergeLoCopyBIncr?] at hcopy
  obtain ⟨entry, hread, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨data, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hfinal with hfinal
  subst next
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (SortSlice.write_read_self_of_eq_some machine.state.data data
    machine.dest entry hwrite).trans hread.symm
  · exact SortSlice.write_readFrame_of_eq_some machine.state.data data
    machine.dest entry hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyDataToTemp_materialized_source_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoMemcpyDataToTemp_materialized_source_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst : Nat}
  {src : Int}
  {materialized : SortSlice kappa nu}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src = some state')
  (hmaterialized : mergeLoTempRun? state'.a dst count = some materialized) :
-- imply
  materialized.entries.size = count ∧ ∀ i, i < count → materialized.entries[i]? = state.data.read? (src + Int.ofNat i) := by
-- proof
  rcases mergeLoTempRun_cells_of_eq_some state'.a dst count materialized
    hmaterialized with ⟨hsize, hcells⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  have hcopied := mergeLoMemcpyDataToTemp_read_range_of_eq_some site hDirection
    count state state' dst src hcopy i hi
  calc
    materialized.entries[i]? = state'.a.cells[dst + i]?.bind id :=
      (hcells i hi).symm
    _ = mergeLoTempRead? state'.a (dst + i) := rfl
    _ = state.data.read? (src + Int.ofNat i) := hcopied

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyTempToData_materialized_source_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeLoMemcpyTempToData_materialized_source_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {dst : Int}
  {src : Nat}
  {materialized : SortSlice kappa nu}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src = some state')
  (hmaterialized : mergeLoTempRun? state.a src count = some materialized) :
-- imply
  materialized.entries.size = count ∧ ∀ i, i < count → state'.data.read? (dst + Int.ofNat i) = materialized.entries[i]? := by
-- proof
  rcases mergeLoTempRun_cells_of_eq_some state.a src count materialized
    hmaterialized with ⟨hsize, hcells⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  have hcopied := mergeLoMemcpyTempToData_read_range_of_eq_some site hDirection
    count state state' dst src hcopy i hi
  calc
    state'.data.read? (dst + Int.ofNat i) =
      mergeLoTempRead? state.a (src + i) := hcopied
    _ = state.a.cells[src + i]?.bind id := rfl
    _ = materialized.entries[i]? := hcells i hi

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiInitialDataToTemp_materialized_source_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiInitialDataToTemp_materialized_source_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {count : Nat}
  {state state' : MergeState kappa nu}
  {src : Int}
  {materialized : SortSlice kappa nu}
-- given
  (hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state 0 src = some state')
  (hmaterialized : initializedTempPrefix? state'.a count = some materialized) :
-- imply
  materialized.entries.size = count ∧ ∀ i, i < count → materialized.entries[i]? = state.data.read? (src + Int.ofNat i) := by
-- proof
  rcases initializedTempPrefix_cells_of_eq_some state'.a count materialized
    hmaterialized with ⟨hsize, hcells⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  have hcopied := mergeHiMemcpyDataToTemp_read_range_of_eq_some
    .initialDataToTemp rfl count state state' 0 src hcopy i hi
  calc
    materialized.entries[i]? = state'.a.cells[i]?.bind id :=
      (hcells i hi).symm
    _ = mergeHiTempRead? state'.a (Int.ofNat i) :=
      (mergeHiTempRead_ofNat state'.a i).symm
    _ = state.data.read? (src + Int.ofNat i) := by simpa using hcopied

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyTempToData_materialized_source_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeHiMemcpyTempToData_materialized_source_of_eq_some
  {kappa : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count tempCount : Nat}
  {state state' : MergeState kappa nu}
  {dst tempSrc : Int}
  {materialized : SortSlice kappa nu}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst tempSrc = some state')
  (hmaterialized : initializedTempPrefix? state.a tempCount = some materialized)
  (htempSrc : 0 ≤ tempSrc)
  (hcontained : tempSrc.toNat + count ≤ tempCount) :
-- imply
  materialized.entries.size = tempCount ∧ ∀ i, i < count → state'.data.read? (dst + Int.ofNat i) = materialized.entries[tempSrc.toNat + i]? := by
-- proof
  rcases initializedTempPrefix_cells_of_eq_some state.a tempCount materialized
    hmaterialized with ⟨hsize, hcells⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  have hcopied := mergeHiMemcpyTempToData_read_range_of_eq_some site hDirection
    count state state' dst tempSrc hcopy i hi
  have hindex :
    tempSrc + Int.ofNat i = Int.ofNat (tempSrc.toNat + i) := by
    rw [← Int.toNat_of_nonneg htempSrc]
    simp
  calc
    state'.data.read? (dst + Int.ofNat i) =
      mergeHiTempRead? state.a (tempSrc + Int.ofNat i) := hcopied
    _ = state.a.cells[tempSrc.toNat + i]?.bind id := by
      rw [hindex, mergeHiTempRead_ofNat]
    _ = materialized.entries[tempSrc.toNat + i]? :=
      hcells (tempSrc.toNat + i) (by omega)

end CPythonListsort

namespace CPythonListsort

/--
[mergeDataMemmove_overlap_snapshot_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeMovementCorrectness.lean)
-/
@[path]
lemma mergeDataMemmove_overlap_snapshot_regression
  {kappa : Type u}
  {nu : Type v} :
-- imply
  mergeDataMemmove? .loCopyBTail mergeMovementOverlapInput 1 0 4 = some { entries := #[{ key := 1, value := some 10 }, { key := 1, value := some 10 }, { key := 2, value := some 20 }, { key := 3, value := some 30 }, { key := 4, value := some 40 }] } := by
-- proof
  decide

end CPythonListsort


-- created on 2026-10-23
