import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Correctness.BinarysortCorrectness.Part3
open CPythonListsort


namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[lt_of_lt_of_not_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
if `a < b` and `c` is not below `b`, then `a < c`. -/
private lemma BoolStrictWeakOrder.lt_of_lt_of_not_lt
  {lt : BoolComparator alpha} (h : BoolStrictWeakOrder lt)
  {a b c : alpha} (hab : lt a b = true) (hcb : lt c b = false) :
  lt a c = true := by
  by_contra hnac
  have hnac' : ¬lt a c = true := hnac
  have hnca : ¬lt c a = true := by
    intro hca
    have hcb' := h.trans c a b hca hab
    rw [hcb] at hcb'
    exact Bool.noConfusion hcb'
  have hac : ¬lt a c = true ∧ ¬lt c a = true := ⟨hnac', hnca⟩
  have hnbc : ¬lt b c = true := by
    intro hbc
    exact hnac' (h.trans a b c hab hbc)
  have hbc : ¬lt b c = true ∧ ¬lt c b = true := by
    exact ⟨hnbc, by simpa using hcb⟩
  exact (h.incomp_trans a c b hac ⟨hbc.2, hbc.1⟩).1 hab

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_toList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_toList (xs : Array beta)
  (insert stop : Nat) (pivot : beta) :
  (insertEarlierEntries xs insert stop pivot).toList =
    ((xs.toList.extract 0 insert ++ [pivot]) ++
      xs.toList.extract insert stop) ++
        xs.toList.extract (stop + 1) xs.size := by
  simp [insertEarlierEntries]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[sortSlice_read_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma sortSlice_read_ofNat (slice : SortSlice kappa rho) (index : Nat) :
  slice.read? (Int.ofNat index) = slice.entries[index]? := by
  simp [SortSlice.read?]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[sortSlice_write_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma sortSlice_write_ofNat (slice : SortSlice kappa rho)
  (index : Nat) (entry : SortSliceEntry kappa rho)
  (hindex : index < slice.entries.size) :
  slice.write? (Int.ofNat index) entry =
    some { entries := slice.entries.set index entry } := by
  simp [SortSlice.write?, hindex]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[sortSlice_copy_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma sortSlice_copy_ofNat (slice : SortSlice kappa rho)
  (dst src : Nat) (hdst : dst < slice.entries.size)
  (hsrc : src < slice.entries.size) :
  slice.copy? (Int.ofNat dst) (Int.ofNat src) =
    some { entries := slice.entries.set dst slice.entries[src] } := by
  rw [SortSlice.copy?, SortSlice.copyFrom?, sortSlice_read_ofNat]
  rw [Array.getElem?_eq_getElem hsrc]
  exact sortSlice_write_ofNat slice dst slice.entries[src] hdst
/-! The next two lemmas isolate the only low-level array calculation needed by
the correctness proof.  They state the exact effect of CPython's high-to-low
overlap-safe shift, not merely its size or safety. -/
set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_set_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_set_high
  (xs : Array beta) (insert count : Nat) (pivot : beta)
  (hfit : insert + (count + 1) < xs.size) :
  insertEarlierEntries
    (xs.set (insert + count + 1) xs[insert + count])
    insert (insert + count) pivot =
    insertEarlierEntries xs insert (insert + count + 1) pivot := by
  apply Array.ext_getElem?
  intro index
  have hinsert : insert <= xs.size := by omega
  have hcount : insert + count <= xs.size := by omega
  have hcount1 : insert + count + 1 <= xs.size := by omega
  have hcount2 : insert + count + 1 + 1 <= xs.size := by omega
  simp only [insertEarlierEntries, Array.getElem?_append, Array.size_append,
    Array.size_extract, Array.size_singleton, Array.size_set]
  simp only [min_eq_left hinsert, min_eq_left hcount, min_eq_left hcount1,
    min_eq_left hcount2, Nat.sub_zero, Nat.add_sub_cancel_left]
  simp only [Array.getElem?_extract, Array.getElem?_singleton,
    Array.getElem?_set]
  split_ifs <;> try omega
  all_goals simp only [Array.size_set, min_eq_left hinsert,
    min_eq_left hcount, min_eq_left hcount1, Nat.zero_add, Nat.sub_zero,
    Nat.add_sub_cancel_left, min_self, if_pos le_rfl] at *
  all_goals try omega
  all_goals try rfl
  all_goals
    first
    | have hindex : index = insert + count + 1 := by omega
      subst index
      simp [hfit]
    | have hbase0 : insert + 1 + count = insert + count + 1 := by omega
      have hbase1 :
        insert + 1 + (insert + count + 1 - insert) =
          insert + count + 1 + 1 := by omega
      rw [hbase0, hbase1] at *
      have hle0 : insert + count + 1 ≤ index := by omega
      have hle1 : insert + count + 1 + 1 ≤ index := by omega
      rw [Nat.add_sub_of_le hle0, Nat.add_sub_of_le hle1]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[memmoveBackward_write_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma memmoveBackward_write_exact
  (slice : SortSlice kappa rho) (insert count : Nat)
  (pivot : SortSliceEntry kappa rho)
  (hfit : insert + count < slice.entries.size) :
  (do
    let shifted <- SortSlice.memmoveBackward? count slice
      (Int.ofNat (insert + 1)) (Int.ofNat insert)
    shifted.write? (Int.ofNat insert) pivot) =
    some ({ entries :=
      insertEarlierEntries slice.entries insert (insert + count) pivot } :
        SortSlice kappa rho) := by
  induction count generalizing slice with
  | zero =>
    simp only [SortSlice.memmoveBackward?]
    change slice.write? (Int.ofNat insert) pivot = _
    rw [sortSlice_write_ofNat slice insert pivot (by omega)]
    simp only [Option.some.injEq, SortSlice.mk.injEq]
    apply Array.ext_getElem?
    intro index
    have hinsert : insert ≤ slice.entries.size := by omega
    simp only [insertEarlierEntries, Nat.add_zero, Array.getElem?_set,
      Array.getElem?_append, Array.size_append, Array.size_extract,
      Array.size_singleton]
    simp only [Nat.sub_zero,
      Array.getElem?_extract, Array.getElem?_singleton]
    split_ifs <;> try omega
    all_goals simp only [min_eq_left hinsert, min_self, Nat.sub_self,
      Nat.zero_add] at *
    all_goals
      first
      | apply Array.getElem?_eq_none
        omega
      | have hle : insert + 1 ≤ index := by omega
        simp only [Nat.add_zero] at *
        rw [Nat.add_sub_of_le hle]
  | succ count ih =>
    simp only [SortSlice.memmoveBackward?]
    have hsrc : insert + count < slice.entries.size := by omega
    have hdst : insert + count + 1 < slice.entries.size := by omega
    rw [show Int.ofNat (insert + 1) + Int.ofNat count =
      Int.ofNat (insert + count + 1) by simp [Int.ofNat_eq_natCast]; omega]
    rw [show Int.ofNat insert + Int.ofNat count =
      Int.ofNat (insert + count) by simp]
    rw [sortSlice_copy_ofNat slice (insert + count + 1)
      (insert + count) hdst hsrc]
    have hsize :
      (slice.entries.set (insert + count + 1) slice.entries[insert + count]).size =
        slice.entries.size := by simp
    have hih := ih ({ entries :=
      slice.entries.set (insert + count + 1) slice.entries[insert + count] } :
        SortSlice kappa rho) (by simpa [hsize] using hsrc)
    change
      (do
        let shifted ← SortSlice.memmoveBackward? count
          ({ entries :=
            slice.entries.set (insert + count + 1) slice.entries[insert + count] } :
              SortSlice kappa rho)
          (Int.ofNat (insert + 1)) (Int.ofNat insert)
        shifted.write? (Int.ofNat insert) pivot) = _
    rw [hih]
    simp only [Option.some.injEq, SortSlice.mk.injEq]
    change insertEarlierEntries
      (slice.entries.set (insert + count + 1) slice.entries[insert + count])
      insert (insert + count) pivot =
      insertEarlierEntries slice.entries insert (insert + (count + 1)) pivot
    simpa only [Nat.add_assoc] using
      insertEarlierEntries_set_high slice.entries insert count pivot hfit

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[memmove_write_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma memmove_write_exact
  (slice : SortSlice kappa rho) (insert count : Nat)
  (pivot : SortSliceEntry kappa rho)
  (hfit : insert + count < slice.entries.size) :
  (do
    let shifted <- slice.memmove? (Int.ofNat (insert + 1))
      (Int.ofNat insert) count
    shifted.write? (Int.ofNat insert) pivot) =
    some ({ entries :=
      insertEarlierEntries slice.entries insert (insert + count) pivot } :
        SortSlice kappa rho) := by
  have hnot : ¬ Int.ofNat (insert + 1) ≤ Int.ofNat insert := by
    intro h
    have := Int.ofNat_le.mp h
    omega
  unfold SortSlice.memmove? SortSlice.memmoveDirection
  rw [if_neg hnot]
  exact memmoveBackward_write_exact slice insert count pivot hfit

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_size (xs : Array beta)
  (insert stop : Nat) (pivot : beta) (hinsert : insert ≤ stop)
  (hstop : stop < xs.size) :
  (insertEarlierEntries xs insert stop pivot).size = xs.size := by
  simp [insertEarlierEntries]
  omega
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_getElem?](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_getElem?
  (xs : Array beta) (insert stop i : Nat) (pivot : beta)
  (hinsert : insert ≤ stop) (hstop : stop < xs.size) :
  (insertEarlierEntries xs insert stop pivot)[i]? =
    if i < insert then xs[i]?
    else if i = insert then some pivot
    else if i ≤ stop then xs[i - 1]?
    else xs[i]? := by
  simp only [insertEarlierEntries, Array.getElem?_append, Array.size_append,
    Array.size_extract, Array.size_singleton, Array.getElem?_extract,
    Array.getElem?_singleton]
  have hinsize : insert ≤ xs.size := by omega
  have hstopsize : stop ≤ xs.size := by omega
  simp only [min_eq_left hinsize, min_eq_left hstopsize,
    Nat.sub_zero]
  split_ifs <;> try omega
  all_goals try simp only [min_self, Nat.zero_add] at *
  all_goals
    first
    | rw [Array.getElem?_eq_getElem (by omega)]
      congr 1 <;> omega
    | congr 1 <;> omega
    | apply Array.getElem?_eq_none
      omega
    | symm
      apply Array.getElem?_eq_none
      omega
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_range
  (xs : Array (SortSliceEntry kappa rho)) (base n position ok : Nat)
  (pivot : SortSliceEntry kappa rho)
  (hpos : position ≤ ok) (hok : ok < n)
  (hstop : base + n ≤ xs.size) :
  sortSliceRangeEntries
    ({ entries := insertEarlierEntries xs (base + position) (base + ok) pivot } :
      SortSlice kappa rho)
    base n =
    insertEarlierEntries
      (sortSliceRangeEntries ({ entries := xs } : SortSlice kappa rho) base n)
      position ok pivot := by
  apply Array.ext_getElem?
  intro i
  have hrangeSize :
    (sortSliceRangeEntries ({ entries := xs } : SortSlice kappa rho) base n).size = n :=
    sortSliceRangeEntries_size _ _ _ hstop
  rw [insertEarlierEntries_getElem? _ position ok i pivot hpos (by omega)]
  simp only [sortSliceRangeEntries, Array.getElem?_extract]
  rw [insertEarlierEntries_size xs (base + position) (base + ok) pivot
    (by omega) (by omega)]
  rw [insertEarlierEntries_getElem? xs (base + position) (base + ok)
    (base + i) pivot (by omega) (by omega)]
  try simp only [hrangeSize]
  split_ifs <;> try omega
  all_goals try rfl
  all_goals
    first
    | congr 1 <;> omega
    | apply Array.getElem?_eq_none
      omega
    | symm
      apply Array.getElem?_eq_none
      omega

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[list_eq_take_getElem_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma list_eq_take_getElem_drop (xs : List beta) (i : Nat)
  (hi : i < xs.length) :
  xs = xs.take i ++ xs[i] :: xs.drop (i + 1) := by
  calc
    xs = xs.take (i + 1) ++ xs.drop (i + 1) :=
      (List.take_append_drop (i + 1) xs).symm
    _ = (xs.take i ++ [xs[i]]) ++ xs.drop (i + 1) := by
      rw [List.take_add_one]
      simp only [List.getElem?_eq_getElem hi, Option.toList_some]
    _ = xs.take i ++ xs[i] :: xs.drop (i + 1) := by simp

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_perm
  (xs : Array beta) (insert stop : Nat) (pivot : beta)
  (hinsert : insert ≤ stop) (hstop : stop < xs.size)
  (hpivot : pivot = xs[stop]) :
  (insertEarlierEntries xs insert stop pivot).toList.Perm xs.toList := by
  let tail := xs.toList.drop insert
  let middle := tail.take (stop - insert)
  let suffix := tail.drop (stop - insert + 1)
  have htailIndex : stop - insert < tail.length := by
    dsimp [tail]
    simp only [List.length_drop, Array.length_toList]
    omega
  have htailPivot : tail[stop - insert] = pivot := by
    dsimp [tail]
    rw [List.getElem_drop]
    have hindex : insert + (stop - insert) = stop := by omega
    simpa only [hindex, Array.getElem_toList] using hpivot.symm
  have htail : tail = middle ++ pivot :: suffix := by
    dsimp [middle, suffix]
    simpa only [htailPivot] using
      list_eq_take_getElem_drop tail (stop - insert) htailIndex
  have hwhole : xs.toList = xs.toList.take insert ++ middle ++ pivot :: suffix := by
    calc
      xs.toList = xs.toList.take insert ++ tail := by
        simpa only [tail] using (List.take_append_drop insert xs.toList).symm
      _ = xs.toList.take insert ++ middle ++ pivot :: suffix := by
        rw [htail]
        simp only [List.append_assoc]
  rw [insertEarlierEntries_toList]
  simp only [List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
  have hextractMiddle :
    (xs.toList.drop insert).take (stop - insert) = middle := rfl
  have hextractSuffix :
    xs.toList.drop (stop + 1) = suffix := by
    dsimp [suffix, tail]
    rw [List.drop_drop]
    congr 1
    omega
  have hsuffixLength : suffix.length = xs.size - (stop + 1) := by
    dsimp [suffix, tail]
    simp only [List.length_drop, Array.length_toList]
    omega
  rw [hextractMiddle, hextractSuffix]
  rw [← hsuffixLength]
  have htakesuffix : suffix.take suffix.length = suffix := by simp
  rw [htakesuffix]
  conv_rhs => rw [hwhole]
  simpa only [List.append_assoc, List.singleton_append, List.cons_append,
    List.nil_append] using
    ((List.perm_middle :
      (middle ++ pivot :: suffix).Perm (pivot :: (middle ++ suffix))).append_left
      (xs.toList.take insert)).symm

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_range_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_range_perm
  (xs : Array (SortSliceEntry kappa rho)) (base n position ok : Nat)
  (pivot : SortSliceEntry kappa rho)
  (hpos : position ≤ ok) (hok : ok < n)
  (hstop : base + n ≤ xs.size)
  (hpivot : pivot = xs[base + ok]) :
  (sortSliceRangeEntries
    ({ entries := insertEarlierEntries xs (base + position) (base + ok) pivot } :
      SortSlice kappa rho) base n).toList.Perm
    (sortSliceRangeEntries ({ entries := xs } : SortSlice kappa rho) base n).toList := by
  rw [insertEarlierEntries_range xs base n position ok pivot hpos hok hstop]
  have hlocalStop :
    ok < (sortSliceRangeEntries ({ entries := xs } : SortSlice kappa rho) base n).size := by
    rwa [sortSliceRangeEntries_size _ _ _ hstop]
  have hget := sortSliceRangeEntries_getElem
    ({ entries := xs } : SortSlice kappa rho) base n ok hstop hok
  have hpivotLocal : pivot =
    (sortSliceRangeEntries ({ entries := xs } : SortSlice kappa rho) base n)[ok] :=
    hpivot.trans hget.symm
  exact insertEarlierEntries_perm _ position ok pivot hpos hlocalStop hpivotLocal

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_frame
  (xs : Array (SortSliceEntry kappa rho)) (base n position ok : Nat)
  (pivot : SortSliceEntry kappa rho)
  (hpos : position ≤ ok) (hok : ok < n)
  (hstop : base + n ≤ xs.size) :
  SortSlice.EqualOutsideRange
    ({ entries := xs } : SortSlice kappa rho)
    ({ entries := insertEarlierEntries xs (base + position) (base + ok) pivot } :
      SortSlice kappa rho)
    base n := by
  have hsize := insertEarlierEntries_size xs (base + position) (base + ok) pivot
    (by omega) (by omega)
  refine ⟨hsize.symm, ?_⟩
  intro otherStart otherCount hdisjoint
  apply Array.ext_getElem?
  intro i
  simp only [sortSliceRangeEntries, Array.getElem?_extract]
  rw [hsize]
  by_cases hi : i < min (otherStart + otherCount) xs.size - otherStart
  · simp only [if_pos hi]
    have hiCount : i < otherCount := by omega
    have hglobal : otherStart + i < xs.size := by omega
    have houtside : otherStart + i < base ∨ base + n ≤ otherStart + i := by
      obtain hbefore | hafter := hdisjoint
      · left; omega
      · right; omega
    rw [insertEarlierEntries_getElem? xs (base + position) (base + ok)
      (otherStart + i) pivot (by omega) (by omega)]
    obtain hbefore | hafter := houtside
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · simp only [if_neg hi]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_get_before](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_get_before
  (xs : Array beta) (insert stop i : Nat) (pivot : beta)
  (hinsert : insert ≤ stop) (hstop : stop < xs.size) (hi : i < insert) :
  (insertEarlierEntries xs insert stop pivot)[i]'(by
    rw [insertEarlierEntries_size xs insert stop pivot hinsert hstop]
    omega) = xs[i]'(by omega) := by
  have hget := insertEarlierEntries_getElem? xs insert stop i pivot hinsert hstop
  have hsize := insertEarlierEntries_size xs insert stop pivot hinsert hstop
  rw [if_pos hi, Array.getElem?_eq_getElem (by rw [hsize]; omega),
    Array.getElem?_eq_getElem (by omega)] at hget
  exact Option.some.inj hget

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_get_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_get_at
  (xs : Array beta) (insert stop : Nat) (pivot : beta)
  (hinsert : insert ≤ stop) (hstop : stop < xs.size) :
  (insertEarlierEntries xs insert stop pivot)[insert]'(by
    rw [insertEarlierEntries_size xs insert stop pivot hinsert hstop]
    omega) = pivot := by
  have hget := insertEarlierEntries_getElem? xs insert stop insert pivot hinsert hstop
  rw [if_neg (Nat.lt_irrefl _), if_pos rfl,
    Array.getElem?_eq_getElem (by
      rw [insertEarlierEntries_size xs insert stop pivot hinsert hstop]
      omega)] at hget
  exact Option.some.inj hget

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_get_shifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_get_shifted
  (xs : Array beta) (insert stop i : Nat) (pivot : beta)
  (hinsert : insert ≤ stop) (hstop : stop < xs.size)
  (hilow : insert < i) (hihigh : i ≤ stop) :
  (insertEarlierEntries xs insert stop pivot)[i]'(by
    rw [insertEarlierEntries_size xs insert stop pivot hinsert hstop]
    omega) = xs[i - 1]'(by omega) := by
  have hget := insertEarlierEntries_getElem? xs insert stop i pivot hinsert hstop
  have hsize := insertEarlierEntries_size xs insert stop pivot hinsert hstop
  rw [if_neg (by omega), if_neg (by omega), if_pos hihigh,
    Array.getElem?_eq_getElem (by rw [hsize]; omega),
    Array.getElem?_eq_getElem (by omega)] at hget
  exact Option.some.inj hget

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[binarysortSearch_semantics](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma binarysortSearch_semantics
  {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
  (slice : SortSlice (Occurrence alpha) nu) (base ok fuel left right : Nat)
  (pivot : SortSliceEntry (Occurrence alpha) nu)
  (hstop : base + ok ≤ slice.entries.size)
  (hsorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys slice base ok))
  (hle : left ≤ right) (hright : right ≤ ok)
  (hwidth : right - left < fuel)
  (hbefore : ∀ i (hi : i < left),
    occurrenceComparator lt pivot.key
      (slice.entries[base + i]'(by
        exact lt_of_lt_of_le
          (Nat.add_lt_add_left (lt_of_lt_of_le hi
            (le_trans hle hright)) base) hstop)).key = false)
  (hafter : ∀ i (_ : right ≤ i) (hi : i < ok),
    occurrenceComparator lt pivot.key
      (slice.entries[base + i]'(by
        exact lt_of_lt_of_le (Nat.add_lt_add_left hi base) hstop)).key = true) :
  ∃ result,
    binarysortSearch? fuel (occurrenceComparator lt) slice
      (Int.ofNat base) pivot left right = some result ∧
      BinarySearchSemanticPost (occurrenceComparator lt) slice base pivot ok result := by
  have hsortedIndex : ∀ i j (hi : i < ok) (hj : j < ok) (_ : i < j),
    occurrenceComparator lt
      (slice.entries[base + j]'(by
        exact lt_of_lt_of_le (Nat.add_lt_add_left hj base) hstop)).key
      (slice.entries[base + i]'(by
        exact lt_of_lt_of_le (Nat.add_lt_add_left hi base) hstop)).key = false := by
    intro i j hi hj hij
    have hi' : i < (sortSliceRangeKeys slice base ok).size := by
      rwa [sortSliceRangeKeys_size slice base ok hstop]
    have hj' : j < (sortSliceRangeKeys slice base ok).size := by
      rwa [sortSliceRangeKeys_size slice base ok hstop]
    have hindex := (sorted_iff_no_later_precedes
      (occurrenceComparator lt) (sortSliceRangeKeys slice base ok)).mp hsorted
      i j hi' hj' hij
    apply Bool.eq_false_of_not_eq_true
    simpa only [sortSliceRangeKeys_getElem slice base ok i hstop hi,
      sortSliceRangeKeys_getElem slice base ok j hstop hj] using hindex
  induction fuel generalizing left right with
  | zero =>
    omega
  | succ fuel ih =>
    rw [binarysortSearch?]
    by_cases hactive : left < right
    · simp only [if_pos hactive]
      let middle := (left + right) / 2
      have hmiddleLower : left ≤ middle := by
        dsimp [middle]
        omega
      have hmiddleUpper : middle < right := by
        dsimp [middle]
        omega
      have hmiddleOk : middle < ok := lt_of_lt_of_le hmiddleUpper hright
      have hread :
        slice.read? (Int.ofNat base + Int.ofNat middle) =
          some slice.entries[base + middle] := by
        rw [show Int.ofNat base + Int.ofNat middle =
          Int.ofNat (base + middle) by simp]
        rw [sortSlice_read_ofNat, Array.getElem?_eq_getElem (by omega)]
      rw [hread]
      simp only [binarysortBindOptionAcross, iflt_eq]
      by_cases hcmp : occurrenceComparator lt pivot.key
        slice.entries[base + middle].key = true
      · simp only [hcmp, if_true]
        have hwidth' : middle - left < fuel := by omega
        have hafter' : ∀ i (_ : middle ≤ i) (hi : i < ok),
          occurrenceComparator lt pivot.key
            (slice.entries[base + i]'(by
              exact lt_of_lt_of_le (Nat.add_lt_add_left hi base) hstop)).key = true := by
          intro i hmi hi
          by_cases him : i = middle
          · subst i
            exact hcmp
          · have hmil : middle < i := lt_of_le_of_ne hmi (Ne.symm him)
            exact (horder.occurrenceComparator.lt_of_lt_of_not_lt hcmp
              (hsortedIndex middle i hmiddleOk hi hmil))
        rcases ih left middle hmiddleLower
          (le_trans (Nat.le_of_lt hmiddleUpper) hright) hwidth' hbefore hafter' with
          ⟨result, heval, hpost⟩
        exact ⟨result, heval, hpost⟩
      · have hcmpFalse : occurrenceComparator lt pivot.key
        slice.entries[base + middle].key = false :=
        Bool.eq_false_of_not_eq_true hcmp
        simp only [hcmpFalse]
        have hwidth' : right - (middle + 1) < fuel := by omega
        have hbefore' : ∀ i (hi : i < middle + 1),
          occurrenceComparator lt pivot.key
            (slice.entries[base + i]'(by
              exact lt_of_lt_of_le
                (Nat.add_lt_add_left (lt_of_lt_of_le hi
                  (le_trans (Nat.succ_le_of_lt hmiddleUpper) hright)) base)
                hstop)).key = false := by
          intro i hi
          by_cases hil : i < left
          · exact hbefore i hil
          · by_cases him : i = middle
            · subst i
              exact hcmpFalse
            · have himl : i < middle := by omega
              apply Bool.eq_false_of_not_eq_true
              intro hpivi
              have hpivm := horder.occurrenceComparator.lt_of_lt_of_not_lt
                hpivi (hsortedIndex i middle (by omega) hmiddleOk himl)
              exact hcmp hpivm
        rcases ih (middle + 1) right (by omega) hright
          hwidth' hbefore' hafter with ⟨result, heval, hpost⟩
        exact ⟨result, heval, hpost⟩
    · have heq : left = right := by omega
      subst right
      rw [if_neg (Nat.lt_irrefl left)]
      let result : BinarySearchResult :=
        { position := left, fuelExhausted := false }
      refine ⟨result, by rfl, ?_⟩
      exact
        { rangeStop := hstop
          fuel := rfl
          positionLe := le_trans hle hright
          beforeFalse := hbefore
          afterTrue := hafter }

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[strict_reverse_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma strict_reverse_false
  {cmp : BoolComparator beta} (horder : BoolStrictWeakOrder cmp)
  {a b : beta} (hab : cmp a b = true) : cmp b a = false := by
  apply Bool.eq_false_iff.mpr
  intro hba
  exact horder.irrefl a (horder.trans a b a hab hba)

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[pairwise_moveEarlier_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma pairwise_moveEarlier_decomposition
  {R : beta → beta → Prop} {A B C : List beta} {pivot : beta}
  (hold : (A ++ B ++ pivot :: C).Pairwise R)
  (hpivotB : ∀ b ∈ B, R pivot b) :
  (A ++ pivot :: (B ++ C)).Pairwise R := by
  have hAB_rest := List.pairwise_append.mp hold
  have hAB := hAB_rest.1
  have hpivotC := List.pairwise_cons.mp hAB_rest.2.1
  have hABparts := List.pairwise_append.mp hAB
  have hBC : (B ++ C).Pairwise R := by
    apply List.pairwise_append.mpr
    refine ⟨hABparts.2.1, hpivotC.2, ?_⟩
    intro b hb c hc
    exact hAB_rest.2.2 b (List.mem_append_right A hb) c
      (by simp only [List.mem_cons]; exact Or.inr hc)
  have hpivotBC : ∀ y ∈ B ++ C, R pivot y := by
    intro y hy
    rw [List.mem_append] at hy
    obtain hy | hy := hy
    · exact hpivotB y hy
    · exact hpivotC.1 y hy
  apply List.pairwise_append.mpr
  refine ⟨hABparts.1, List.pairwise_cons.mpr ⟨hpivotBC, hBC⟩, ?_⟩
  intro a ha y hy
  rw [List.mem_cons] at hy
  obtain rfl | hy := hy
  · exact hAB_rest.2.2 a (List.mem_append_left B ha) y List.mem_cons_self
  · rw [List.mem_append] at hy
    obtain hy | hy := hy
    · exact hABparts.2.2 a ha y hy
    · exact hAB_rest.2.2 a (List.mem_append_left B ha) y
      (List.mem_cons_of_mem pivot hy)

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[take_split_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma take_split_at (xs : List beta) {p k : Nat} (hpk : p ≤ k) :
  xs.take p ++ (xs.drop p).take (k - p) = xs.take k := by
  calc
    xs.take p ++ (xs.drop p).take (k - p) =
      (xs.take k).take p ++ (xs.take k).drop p := by
      rw [List.drop_take]
      simp only [List.take_take, min_eq_left hpk]
    _ = xs.take k := List.take_append_drop p (xs.take k)

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[moveEarlier_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma moveEarlier_take
  (xs : List beta) (p k : Nat) (pivot : beta)
  (hpk : p ≤ k) (hk : k < xs.length) :
  (moveEarlier xs p k pivot).take (k + 1) =
    xs.take p ++ pivot :: (xs.drop p).take (k - p) := by
  have hpLength : (xs.take p).length = p := by simp; omega
  have hmiddleLength : ((xs.drop p).take (k - p)).length = k - p := by
    simp
    omega
  have hprefixLength :
    (xs.take p ++ pivot :: (xs.drop p).take (k - p)).length = k + 1 := by
    simp [hpLength, hmiddleLength]
    omega
  unfold moveEarlier
  rw [show xs.take p ++ pivot ::
    ((xs.drop p).take (k - p) ++ xs.drop (k + 1)) =
      (xs.take p ++ pivot :: (xs.drop p).take (k - p)) ++
        xs.drop (k + 1) by simp only [List.append_assoc, List.cons_append]]
  rwa [← hprefixLength]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[moveEarlier_sortedPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma moveEarlier_sortedPrefix
  (cmp : BoolComparator beta) (horder : BoolStrictWeakOrder cmp)
  (xs : List beta) (p k : Nat) (pivot : beta)
  (hpk : p ≤ k) (hk : k < xs.length)
  (hsorted : (xs.take k).Pairwise fun a b => cmp b a = false)
  (hbefore : ∀ i (hi : i < p), cmp pivot (xs[i]'(by omega)) = false)
  (hcrossed : ∀ i (_ : p ≤ i) (hik : i < k),
    cmp pivot (xs[i]'(by omega)) = true) :
  ((moveEarlier xs p k pivot).take (k + 1)).Pairwise fun a b =>
    cmp b a = false := by
  let A := xs.take p
  let B := (xs.drop p).take (k - p)
  have hAB : (A ++ B).Pairwise fun a b => cmp b a = false := by
    rwa [show A ++ B = xs.take k by simpa [A, B] using take_split_at xs hpk]
  have hpLength : p ≤ xs.length := by omega
  have hleft : ∀ a ∈ A, cmp pivot a = false := by
    intro a ha
    rw [List.mem_take_iff_getElem] at ha
    obtain ⟨i, hi, hia⟩ := ha
    have hip : i < p := by simpa [A, min_eq_left hpLength] using hi
    rw [← hia]
    exact hbefore i hip
  have hright : ∀ b ∈ B, cmp b pivot = false := by
    intro b hb
    rw [List.mem_take_iff_getElem] at hb
    obtain ⟨j, hj, hjb⟩ := hb
    have hdropLength : k - p ≤ (xs.drop p).length := by simp; omega
    have hjmiddle : j < k - p := lt_of_lt_of_le hj (min_le_left _ _)
    have hjdrop : j < (xs.drop p).length := lt_of_lt_of_le hjmiddle hdropLength
    have hindex : p + j < k := by omega
    have hstrict := hcrossed (p + j) (by omega) hindex
    have hget : (xs.drop p)[j] = xs[p + j] := List.getElem_drop
    rw [← hjb, hget]
    exact strict_reverse_false horder hstrict
  have hnew : (A ++ pivot :: B).Pairwise fun a b => cmp b a = false := by
    have hparts := List.pairwise_append.mp hAB
    apply List.pairwise_append.mpr
    refine ⟨hparts.1, List.pairwise_cons.mpr ⟨hright, hparts.2.1⟩, ?_⟩
    intro a ha y hy
    rw [List.mem_cons] at hy
    obtain rfl | hy := hy
    · exact hleft a ha
    · exact hparts.2.2 a ha y hy
  rwa [moveEarlier_take xs p k pivot hpk hk]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[moveEarlier_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma moveEarlier_decomposition
  (xs : List beta) (p k : Nat) (pivot : beta)
  (hpk : p ≤ k) (hk : k < xs.length) (hpivot : pivot = xs[k]) :
  xs = xs.take p ++ (xs.drop p).take (k - p) ++
    pivot :: xs.drop (k + 1) := by
  calc
    xs = xs.take k ++ xs[k] :: xs.drop (k + 1) :=
      list_eq_take_getElem_drop xs k hk
    _ = (xs.take p ++ (xs.drop p).take (k - p)) ++
      pivot :: xs.drop (k + 1) := by
      rw [take_split_at xs hpk, hpivot]
    _ = xs.take p ++ (xs.drop p).take (k - p) ++
      pivot :: xs.drop (k + 1) := by simp only [List.append_assoc]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[moveEarlier_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma moveEarlier_pairwise
  {R : beta → beta → Prop} (xs : List beta) (p k : Nat) (pivot : beta)
  (hpk : p ≤ k) (hk : k < xs.length) (hpivot : pivot = xs[k])
  (hold : xs.Pairwise R)
  (hpivotCrossed : ∀ b ∈ (xs.drop p).take (k - p), R pivot b) :
  (moveEarlier xs p k pivot).Pairwise R := by
  have hdecomp := moveEarlier_decomposition xs p k pivot hpk hk hpivot
  rw [hdecomp] at hold
  unfold moveEarlier
  exact pairwise_moveEarlier_decomposition hold hpivotCrossed

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[moveEarlier_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma moveEarlier_perm
  (xs : List beta) (p k : Nat) (pivot : beta)
  (hpk : p ≤ k) (hk : k < xs.length) (hpivot : pivot = xs[k]) :
  (moveEarlier xs p k pivot).Perm xs := by
  have hdecomp := moveEarlier_decomposition xs p k pivot hpk hk hpivot
  unfold moveEarlier
  conv_rhs => rw [hdecomp]
  simpa only [List.append_assoc, List.cons_append] using
    ((List.perm_middle :
      ((xs.drop p).take (k - p) ++ pivot :: xs.drop (k + 1)).Perm
        (pivot :: ((xs.drop p).take (k - p) ++ xs.drop (k + 1)))).append_left
          (xs.take p)).symm

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_range_toList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_range_toList
  (xs : Array (SortSliceEntry kappa rho)) (base n position ok : Nat)
  (pivot : SortSliceEntry kappa rho)
  (hpos : position ≤ ok) (hok : ok < n)
  (hstop : base + n ≤ xs.size) :
  (sortSliceRangeEntries
    ({ entries := insertEarlierEntries xs (base + position) (base + ok) pivot } :
      SortSlice kappa rho) base n).toList =
    moveEarlier
      (sortSliceRangeEntries ({ entries := xs } : SortSlice kappa rho) base n).toList
      position ok pivot := by
  rw [insertEarlierEntries_range xs base n position ok pivot hpos hok hstop]
  rw [insertEarlierEntries_toList]
  simp only [moveEarlier, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
  have hrangeSize := sortSliceRangeEntries_size
    ({ entries := xs } : SortSlice kappa rho) base n hstop
  have hsuffix :
    ((sortSliceRangeEntries ({ entries := xs } : SortSlice kappa rho) base n).toList.drop
      (ok + 1)).take
        ((sortSliceRangeEntries ({ entries := xs } : SortSlice kappa rho) base n).size -
          (ok + 1)) =
      (sortSliceRangeEntries ({ entries := xs } : SortSlice kappa rho) base n).toList.drop
        (ok + 1) := by
    simp
  rw [hsuffix]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[sortSliceRangeKeys_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma sortSliceRangeKeys_prefix
  (slice : SortSlice kappa rho) (base count n : Nat)
  (hcount : count ≤ n) (_hstop : base + n ≤ slice.entries.size) :
  (sortSliceRangeKeys slice base count).toList =
    (sortSliceRangeKeys slice base n).toList.take count := by
  rw [sortSliceRangeKeys_toList, sortSliceRangeKeys_toList]
  simp [List.take_take, min_eq_left hcount]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_rangeKeys_toList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_rangeKeys_toList
  (xs : Array (SortSliceEntry kappa rho)) (base n position ok : Nat)
  (pivot : SortSliceEntry kappa rho)
  (hpos : position ≤ ok) (hok : ok < n)
  (hstop : base + n ≤ xs.size) :
  (sortSliceRangeKeys
    ({ entries := insertEarlierEntries xs (base + position) (base + ok) pivot } :
      SortSlice kappa rho) base n).toList =
    moveEarlier
      (sortSliceRangeKeys ({ entries := xs } : SortSlice kappa rho) base n).toList
      position ok pivot.key := by
  simp only [sortSliceRangeKeys, Array.toList_map]
  rw [insertEarlierEntries_range_toList xs base n position ok pivot hpos hok hstop]
  simp [moveEarlier]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_sorted_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_sorted_succ
  {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
  (slice : SortSlice (Occurrence alpha) nu) (base n ok position : Nat)
  (pivot : SortSliceEntry (Occurrence alpha) nu)
  (hstop : base + n ≤ slice.entries.size) (hok : ok < n)
  (hposition : position ≤ ok)
  (hsorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys slice base ok))
  (hbefore : ∀ i (hi : i < position),
    occurrenceComparator lt pivot.key
      (slice.entries[base + i]'(by
        exact lt_of_lt_of_le
          (Nat.add_lt_add_left (lt_of_lt_of_le hi (le_trans hposition
            (Nat.le_of_lt hok))) base) hstop)).key = false)
  (hcrossed : ∀ i (_ : position ≤ i) (hi : i < ok),
    occurrenceComparator lt pivot.key
      (slice.entries[base + i]'(by
        exact lt_of_lt_of_le
          (Nat.add_lt_add_left (lt_trans hi hok) base) hstop)).key = true) :
  Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys
      ({ entries := (insertEarlierEntries slice.entries
        (base + position) (base + ok) pivot) } :
        SortSlice (Occurrence alpha) nu) base (ok + 1)) := by
  let beforeKeys := (sortSliceRangeKeys slice base n).toList
  have hbeforeKeysLength : beforeKeys.length = n := by
    change (sortSliceRangeKeys slice base n).toList.length = n
    rw [Array.length_toList, sortSliceRangeKeys_size slice base n hstop]
  have hsortedPrefix :
    (beforeKeys.take ok).Pairwise fun a b =>
      occurrenceComparator lt b a = false := by
    unfold Sorted at hsorted
    rwa [sortSliceRangeKeys_prefix slice base ok n (by omega) hstop] at hsorted
  have hbeforeKeys : ∀ i (hi : i < position),
    occurrenceComparator lt pivot.key (beforeKeys[i]'(by omega)) = false := by
    intro i hi
    have hget : beforeKeys[i]'(by omega) =
      (slice.entries[base + i]'(by omega)).key := by
      dsimp only [beforeKeys]
      rw [Array.getElem_toList]
      exact sortSliceRangeKeys_getElem slice base n i hstop (by omega)
    rw [hget]
    exact hbefore i hi
  have hcrossedKeys : ∀ i (_ : position ≤ i) (hi : i < ok),
    occurrenceComparator lt pivot.key (beforeKeys[i]'(by omega)) = true := by
    intro i hpi hi
    have hget : beforeKeys[i]'(by omega) =
      (slice.entries[base + i]'(by omega)).key := by
      dsimp only [beforeKeys]
      rw [Array.getElem_toList]
      exact sortSliceRangeKeys_getElem slice base n i hstop (by omega)
    rw [hget]
    exact hcrossed i hpi hi
  have hmoved := moveEarlier_sortedPrefix (occurrenceComparator lt)
    horder.occurrenceComparator beforeKeys position ok pivot.key hposition
    (by omega) hsortedPrefix hbeforeKeys hcrossedKeys
  unfold Sorted
  have hmovedSize := insertEarlierEntries_size slice.entries
    (base + position) (base + ok) pivot (by omega) (by omega)
  rw [sortSliceRangeKeys_prefix
    ({ entries := (insertEarlierEntries slice.entries
      (base + position) (base + ok) pivot) } : SortSlice (Occurrence alpha) nu)
    base (ok + 1) n (by omega) (by rw [hmovedSize]; exact hstop)]
  rw [insertEarlierEntries_rangeKeys_toList slice.entries base n position ok pivot
    hposition hok hstop]
  exact hmoved

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[insertEarlierEntries_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma insertEarlierEntries_stable
  {lt : BoolComparator alpha}
  (slice : SortSlice (Occurrence alpha) nu) (base n ok position : Nat)
  (pivot : SortSliceEntry (Occurrence alpha) nu)
  (canonical : List (Occurrence alpha))
  (hstop : base + n ≤ slice.entries.size) (hok : ok < n)
  (hposition : position ≤ ok)
  (hpivot : pivot = slice.entries[base + ok])
  (hstable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys slice base n).toList)
  (hcrossed : ∀ i (_ : position ≤ i) (hi : i < ok),
    occurrenceComparator lt pivot.key
      (slice.entries[base + i]'(by
        exact lt_of_lt_of_le (Nat.add_lt_add_left (lt_trans hi hok) base) hstop)).key =
          true) :
  StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys
      ({ entries := (insertEarlierEntries slice.entries
        (base + position) (base + ok) pivot) } :
        SortSlice (Occurrence alpha) nu) base n).toList := by
  let beforeKeys := (sortSliceRangeKeys slice base n).toList
  have hbeforeKeysLength : beforeKeys.length = n := by
    change (sortSliceRangeKeys slice base n).toList.length = n
    rw [Array.length_toList, sortSliceRangeKeys_size slice base n hstop]
  have hpivotKey : pivot.key = beforeKeys[ok]'(by omega) := by
    have hget : beforeKeys[ok]'(by omega) =
      (slice.entries[base + ok]'(by omega)).key := by
      dsimp only [beforeKeys]
      rw [Array.getElem_toList]
      exact sortSliceRangeKeys_getElem slice base n ok hstop hok
    rw [hget, hpivot]
  have hpivotCrossed : ∀ b ∈ (beforeKeys.drop position).take (ok - position),
    ComparatorEquivalent lt pivot.key.value b.value → pivot.key.origin < b.origin := by
    intro b hb
    rw [List.mem_take_iff_getElem] at hb
    obtain ⟨j, hj, hjb⟩ := hb
    have hdropLength : ok - position ≤ (beforeKeys.drop position).length := by
      simp only [List.length_drop, hbeforeKeysLength]
      omega
    have hjmiddle : j < ok - position := lt_of_lt_of_le hj (min_le_left _ _)
    have hjdrop : j < (beforeKeys.drop position).length :=
      lt_of_lt_of_le hjmiddle hdropLength
    have habsolute : position + j < ok := by omega
    have hstrict := hcrossed (position + j) (by omega) habsolute
    have hgetDrop : (beforeKeys.drop position)[j] = beforeKeys[position + j] :=
      List.getElem_drop
    have hgetGlobal : beforeKeys[position + j]'(by omega) =
      (slice.entries[base + (position + j)]'(by omega)).key := by
      dsimp only [beforeKeys]
      rw [Array.getElem_toList]
      exact sortSliceRangeKeys_getElem slice base n (position + j) hstop (by omega)
    rw [← hjb, hgetDrop, hgetGlobal]
    intro hequiv
    have hfalse := hequiv.1
    change lt pivot.key.value
      (slice.entries[base + (position + j)]'(by omega)).key.value = true at hstrict
    rw [hfalse] at hstrict
    exact False.elim (Bool.noConfusion hstrict)
  have hpairwise := moveEarlier_pairwise beforeKeys position ok pivot.key
    hposition (by omega) hpivotKey hstable.2 hpivotCrossed
  have hperm := moveEarlier_perm beforeKeys position ok pivot.key
    hposition (by omega) hpivotKey
  rw [insertEarlierEntries_rangeKeys_toList slice.entries base n position ok pivot
    hposition hok hstop]
  exact ⟨hperm.trans hstable.1, hpairwise⟩

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[binarysortLoop_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma binarysortLoop_correct
  {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
  (canonical : List (Occurrence alpha))
  (state : MergeState (Occurrence alpha) nu)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (slice : SortSlice (Occurrence alpha) nu) (base n ok fuel : Nat)
  (hok : ok ≤ n) (hremaining : n - ok ≤ fuel)
  (hstop : base + n ≤ slice.entries.size)
  (hsorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys slice base ok))
  (hstable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys slice base n).toList) :
  ∃ result, BinarysortLoopCorrectnessPost lt canonical state slice base n ok fuel result := by
  induction fuel generalizing slice ok with
  | zero =>
    have heq : ok = n := by omega
    subst ok
    let result : BinarysortResult (Occurrence alpha) nu :=
      { slice := slice, fuelExhausted := false }
    refine ⟨result, ?_⟩
    exact
      { resultEq := by simp [binarysortLoop?, result]
        resultFuel := rfl
        sorted := hsorted
        stable := hstable
        rangeEntriesPerm := List.Perm.refl _
        frame := SortSlice.EqualOutsideRange.refl slice base n }
  | succ fuel ih =>
    by_cases hactive : ok < n
    · have hpivotBound : base + ok < slice.entries.size := by omega
      let pivot := slice.entries[base + ok]
      have hread : slice.read? (Int.ofNat base + Int.ofNat ok) = some pivot := by
        rw [show Int.ofNat base + Int.ofNat ok = Int.ofNat (base + ok) by simp]
        rw [sortSlice_read_ofNat, Array.getElem?_eq_getElem hpivotBound]
      have hprefixStop : base + ok ≤ slice.entries.size := by omega
      rcases binarysortSearch_semantics horder slice base ok (ok + 1) 0 ok pivot
        hprefixStop hsorted (by omega) (by omega) (by omega)
        (by intro i hi; omega) (by intro i hlow hi; omega) with
        ⟨search, hsearchEval, hsearch⟩
      have hsearchEval' :
        binarysortSearch? (ok + 1) state.key_compare slice (Int.ofNat base)
          pivot 0 ok = some search := by
        rwa [hcompare]
      let nextSlice : SortSlice (Occurrence alpha) nu :=
        { entries := insertEarlierEntries slice.entries
          (base + search.position) (base + ok) pivot }
      have hsum : base + search.position + (ok - search.position) = base + ok := by
        have hpos : search.position ≤ ok := hsearch.positionLe
        omega
      have hmove :
        (do
          let shifted ← slice.memmove?
            (Int.ofNat base + Int.ofNat (search.position + 1))
            (Int.ofNat base + Int.ofNat search.position)
            (ok - search.position)
          shifted.write?
            (Int.ofNat base + Int.ofNat search.position) pivot) =
          some nextSlice := by
        have hexact := memmove_write_exact slice (base + search.position)
          (ok - search.position) pivot (by rw [hsum]; exact hpivotBound)
        have hdst :
          Int.ofNat base + Int.ofNat (search.position + 1) =
            Int.ofNat (base + search.position + 1) := by
          simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
          omega
        have hsrc : Int.ofNat base + Int.ofNat search.position =
          Int.ofNat (base + search.position) := by simp
        rw [hdst, hsrc]
        rw [hsum] at hexact
        simpa only [nextSlice] using hexact
      have hmove' : Option.bind
        (slice.memmove?
          (Int.ofNat base + Int.ofNat (search.position + 1))
          (Int.ofNat base + Int.ofNat search.position)
          (ok - search.position))
        (fun shifted => shifted.write?
          (Int.ofNat base + Int.ofNat search.position) pivot) =
          some nextSlice := by
        exact hmove
      have hnextSize : nextSlice.entries.size = slice.entries.size := by
        dsimp only [nextSlice]
        exact insertEarlierEntries_size slice.entries (base + search.position)
          (base + ok) pivot (by omega) hpivotBound
      have hnextStop : base + n ≤ nextSlice.entries.size := by
        rwa [hnextSize]
      have hnextSorted : Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys nextSlice base (ok + 1)) := by
        dsimp only [nextSlice]
        apply insertEarlierEntries_sorted_succ horder slice base n ok search.position pivot
          hstop hactive hsearch.positionLe hsorted
        · exact hsearch.beforeFalse
        · exact hsearch.afterTrue
      have hpivot : pivot = slice.entries[base + ok] := rfl
      have hnextStable : StableOccurrencePermutation lt canonical
        (sortSliceRangeKeys nextSlice base n).toList := by
        dsimp only [nextSlice]
        exact insertEarlierEntries_stable slice base n ok search.position pivot canonical
          hstop hactive hsearch.positionLe hpivot hstable hsearch.afterTrue
      have hremaining' : n - (ok + 1) ≤ fuel := by omega
      rcases ih nextSlice (ok + 1) (by omega) hremaining' hnextStop
        hnextSorted hnextStable with ⟨result, hrec⟩
      have hstepPerm :
        (sortSliceRangeEntries nextSlice base n).toList.Perm
          (sortSliceRangeEntries slice base n).toList := by
        dsimp only [nextSlice]
        exact insertEarlierEntries_range_perm slice.entries base n search.position ok
          pivot hsearch.positionLe hactive hstop hpivot
      have hstepFrame : SortSlice.EqualOutsideRange slice nextSlice base n := by
        dsimp only [nextSlice]
        exact insertEarlierEntries_frame slice.entries base n search.position ok pivot
          hsearch.positionLe hactive hstop
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
          rw [binarysortLoop?, if_pos hactive, hread]
          simp only [binarysortBindOptionAcross]
          rw [hsearchEval']
          simp only
          rw [hsearch.fuel]
          simp only [Bool.false_eq_true, if_false]
          change Option.bind
            (slice.memmove?
              (Int.ofNat base + Int.ofNat (search.position + 1))
              (Int.ofNat base + Int.ofNat search.position)
              (ok - search.position))
            (fun shifted => Option.bind
              (shifted.write?
                (Int.ofNat base + Int.ofNat search.position) pivot)
              (fun updated => binarysortLoop? fuel state updated
                (Int.ofNat base) n (ok + 1))) = some result
          rwa [← Option.bind_assoc, hmove', Option.bind_some]
          resultFuel := hrec.resultFuel
          sorted := hrec.sorted
          stable := hrec.stable
          rangeEntriesPerm := hrec.rangeEntriesPerm.trans hstepPerm
          frame := hstepFrame.trans hrec.frame }
    · have heq : ok = n := Nat.le_antisymm hok (Nat.le_of_not_gt hactive)
      subst ok
      let result : BinarysortResult (Occurrence alpha) nu :=
        { slice := slice, fuelExhausted := false }
      refine ⟨result, ?_⟩
      exact
        { resultEq := by simp [binarysortLoop?, result]
          resultFuel := rfl
          sorted := hsorted
          stable := hstable
          rangeEntriesPerm := List.Perm.refl _
          frame := SortSlice.EqualOutsideRange.refl slice base n }

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[binarysort_raw_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma binarysort_raw_correct
  {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
  (canonical : List (Occurrence alpha))
  (state : MergeState (Occurrence alpha) nu)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (slice : SortSlice (Occurrence alpha) nu) (base n ok : Nat)
  (hnPositive : 1 ≤ n) (hok : ok ≤ n) (hnMax : n ≤ MAX_MINRUN.toNat)
  (hstop : base + n ≤ slice.entries.size)
  (hsorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys slice base ok))
  (hstable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys slice base n).toList) :
  ∃ result,
    binarysort? state slice (Int.ofNat base) n ok = some result ∧
      result.fuelExhausted = false ∧
      Sorted (occurrenceComparator lt) (sortSliceRangeKeys result.slice base n) ∧
      StableOccurrencePermutation lt canonical
        (sortSliceRangeKeys result.slice base n).toList ∧
      (sortSliceRangeEntries result.slice base n).toList.Perm
        (sortSliceRangeEntries slice base n).toList ∧
      SortSlice.EqualOutsideRange slice result.slice base n := by
  let normalizedOk := if ok = 0 then 1 else ok
  have hnormalized : normalizedOk ≤ n := by
    dsimp [normalizedOk]
    split
    · exact hnPositive
    · exact hok
  have hnormalizedSorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys slice base normalizedOk) := by
    dsimp [normalizedOk]
    split
    · rename_i hzero
      rw [sorted_iff_no_later_precedes]
      intro i j hi hj hij
      have hsize : (sortSliceRangeKeys slice base 1).size = 1 :=
        sortSliceRangeKeys_size slice base 1 (by omega)
      change i < (sortSliceRangeKeys slice base 1).size at hi
      change j < (sortSliceRangeKeys slice base 1).size at hj
      rw [hsize] at hi hj
      omega
    · exact hsorted
  rcases binarysortLoop_correct horder canonical state hcompare slice base n normalizedOk n
    hnormalized (Nat.sub_le _ _) hstop hnormalizedSorted hstable with
    ⟨result, hloop⟩
  have hadmitted : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat :=
    ⟨hnPositive, hok, hnMax⟩
  refine ⟨result, ?_, hloop.resultFuel, hloop.sorted, hloop.stable,
    hloop.rangeEntriesPerm, hloop.frame⟩
  simpa only [binarysort?, if_pos hadmitted, normalizedOk] using hloop.resultEq

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}
/--
[getElem?_eq_of_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
private lemma SortSlice.EqualOutsideRange.getElem?_eq_of_outside
  {before after : SortSlice kappa rho} {start count k : Nat}
  (h : SortSlice.EqualOutsideRange before after start count)
  (houtside : k < start ∨ start + count ≤ k) :
  before.entries[k]? = after.entries[k]? := by
  by_cases hk : k < before.entries.size
  · have hkAfter : k < after.entries.size := by
    rwa [← h.size_eq]
    have hrange := h.entries_eq_of_disjoint k 1 (by
      obtain hbefore | hafter := houtside
      · exact Or.inl (by omega)
      · exact Or.inr hafter)
    have hzero := congrArg (fun entries => entries[0]?) hrange
    simpa [sortSliceRangeEntries, Array.getElem?_extract, hk, hkAfter] using hzero
  · have hk' : before.entries.size ≤ k := Nat.le_of_not_gt hk
    have hkAfter : after.entries.size ≤ k := by
      rwa [← h.size_eq]
    rw [Array.getElem?_eq_none hk', Array.getElem?_eq_none hkAfter]

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
lemma binarysort_correct
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {canonical : List (Occurrence alpha)}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base n ok : Nat}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hnPositive : 1 ≤ n)
  (hok : ok ≤ n)
  (hnMax : n ≤ MAX_MINRUN.toNat)
  (hrange : SortSlice.RangeInBounds slice (Int.ofNat base) n)
  (hmode : SortSlice.ValuesModeInvariant state.a.hasValues slice)
  (hsorted : Sorted (occurrenceComparator lt) (sortSliceRangeKeys slice base ok))
  (hstable : StableOccurrencePermutation lt canonical (sortSliceRangeKeys slice base n).toList) :
-- imply
  ∃ result, BinarysortCorrectnessPost lt canonical state slice base n ok result := by
-- proof
  have hstop : base + n ≤ slice.entries.size := by
    obtain ⟨_, hend⟩ := hrange
    apply Int.ofNat_le.mp
    rw [Int.natCast_add]
    simpa only [Int.ofNat_eq_natCast] using hend
  rcases binarysort_safe state slice (Int.ofNat base) n ok hnPositive hok hnMax
    hrange hmode with ⟨result, hsafety⟩
  have hraw : binarysort? state slice (Int.ofNat base) n ok = some result := by
    have hresult := hsafety.resultEq
    change (binarysortTraced? state slice (Int.ofNat base) n ok).erase =
      some result at hresult
    rwa [hsafety.exactErasure] at hresult
  rcases binarysort_raw_correct horder canonical state hcompare slice base n ok
    hnPositive hok hnMax hstop hsorted hstable with
    ⟨rawResult, hrawResult, _hrawFuel, hresultSorted, hresultStable,
      hresultPerm, hresultFrame⟩
  rw [hraw] at hrawResult
  injection hrawResult with heq
  subst rawResult
  refine ⟨result, hsafety, hresultSorted, hresultStable, hresultPerm,
    hresultFrame, ?_, ?_⟩
  · intro k hk
    exact (hresultFrame.getElem?_eq_of_outside (Or.inl hk)).symm
  · intro k hk
    exact (hresultFrame.getElem?_eq_of_outside (Or.inr hk)).symm

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_correctness_equality_right_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
lemma binarysort_correctness_equality_right_regression
  {alpha : Type u}
  {nu : Type v} :
-- imply
  (binarysortSearchTraced? 4 binarysortCorrectnessEqualState.key_compare binarysortCorrectnessEqualSlice 0 { key := { value := 1, origin := 3 }, value := some 12 } 0 3).result.map (fun result => (result.position, result.fuelExhausted)) = some (2, false) ∧ (binarysortTraced? binarysortCorrectnessEqualState binarysortCorrectnessEqualSlice 0 4 3).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, [{ key := { value := 1, origin := 0 }, value := some 10 }, { key := { value := 1, origin := 1 }, value := some 11 }, { key := { value := 1, origin := 3 }, value := some 12 }, { key := { value := 2, origin := 2 }, value := some 20 }]) := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_correctness_nonzero_base_sentinel_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean)
-/
@[path]
lemma binarysort_correctness_nonzero_base_sentinel_regression
  {alpha : Type u}
  {nu : Type v} :
-- imply
  (binarysortTraced? binarysortCorrectnessOffsetState binarysortCorrectnessOffsetSlice 1 3 1).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, [{ key := { value := 99, origin := 90 }, value := some 900 }, { key := { value := 1, origin := 1 }, value := some 10 }, { key := { value := 2, origin := 0 }, value := some 20 }, { key := { value := 2, origin := 2 }, value := some 21 }, { key := { value := 88, origin := 91 }, value := some 800 }]) := by
-- proof
  decide

end CPythonListsort


-- created on 2026-10-23
