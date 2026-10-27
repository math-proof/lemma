import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Transcription.MergeInitStorage
open CPythonListsort


namespace CPythonListsort

/--
[mergeInitTempCapacity_keyed_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeInitStorage.lean)
-/
@[path]
lemma mergeInitTempCapacity_keyed_toNat
  {κ : Type u}
  {ν : Type v}
  {listSize : PySSize}
-- given
  (hmax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  (mergeInitTempCapacity listSize true).toNat = min ((listSize.toNat + 1) / 2) 128 := by
-- proof
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hmax
  let requested : PySSize := (listSize + 1).sdiv 2
  have hOneNat : (1 : PySSize).toNat = 1 := by rfl
  have hTwoNat : (2 : PySSize).toNat = 2 := by rfl
  have hListSucc : listSize.toNat + 1 < 2 ^ 63 := by
    exact lt_of_le_of_lt (Nat.add_le_add_right hmax 1) (by norm_num)
  have hAddNat : (listSize + 1).toNat = listSize.toNat + 1 := by
    rw [BitVec.toNat_add, hOneNat,
      Nat.mod_eq_of_lt (lt_trans hListSucc (by norm_num : 2 ^ 63 < 2 ^ 64))]
  have hAddMsb : (listSize + 1).msb = false := by
    rw [BitVec.msb_eq_decide, decide_eq_false_iff_not, hAddNat]
    exact Nat.not_le_of_lt hListSucc
  have hTwoMsb : (2 : PySSize).msb = false := by decide
  have hRequestedNat : requested.toNat = (listSize.toNat + 1) / 2 := by
    rw [show requested = (listSize + 1).sdiv 2 from rfl, BitVec.toNat_sdiv]
    simp only [hAddMsb, hTwoMsb]
    change (listSize + 1).toNat / (2 : PySSize).toNat = _
    rw [hAddNat, hTwoNat]
  have hRequestedLt : requested.toNat < 2 ^ 63 := by
    rw [hRequestedNat]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hListSucc
  have hRequestedMsb : requested.msb = false := by
    rw [BitVec.msb_eq_decide, decide_eq_false_iff_not]
    exact Nat.not_le_of_lt hRequestedLt
  have hCapNat :
    (BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2)).toNat = 128 := by
    norm_num [MERGESTATE_TEMP_SIZE]
  have hCapMsb :
    (BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2)).msb = false := by
    rw [BitVec.msb_eq_decide, decide_eq_false_iff_not, hCapNat]
    norm_num
  simp only [mergeInitTempCapacity]
  change (if (BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2)).slt requested then
    BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2) else requested).toNat = _
  rw [BitVec.slt_eq_ult_of_msb_eq (hCapMsb.trans hRequestedMsb.symm)]
  simp only [BitVec.ult, decide_eq_true_eq]
  split <;> rename_i hComparison
  · rw [hCapNat, Nat.min_eq_right]
    rw [hRequestedNat] at hComparison
    omega
  · rw [hRequestedNat, Nat.min_eq_left]
    rw [hCapNat, hRequestedNat] at hComparison
    omega

end CPythonListsort

namespace CPythonListsort

/--
[mergeInitTemp_keyed_alloced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeInitStorage.lean)
-/
@[path]
lemma mergeInitTemp_keyed_alloced
  {κ : Type u}
  {ν : Type v}
  {listSize : PySSize}
-- given
  (hmax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  (mergeInitTemp (κ := κ) (ν := ν) listSize true).alloced.toNat = min ((listSize.toNat + 1) / 2) 128 := by
-- proof
  simpa only [mergeInitTemp] using mergeInitTempCapacity_keyed_toNat listSize hmax

end CPythonListsort

namespace CPythonListsort

/--
[mergeInitTemp_unkeyed_alloced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeInitStorage.lean)
-/
@[path]
lemma mergeInitTemp_unkeyed_alloced
  {κ : Type u}
  {ν : Type v}
  {listSize : PySSize} :
-- imply
  (mergeInitTemp (κ := κ) (ν := ν) listSize false).alloced.toNat = 256 := by
-- proof
  simp [mergeInitTemp, mergeInitTempCapacity, MERGESTATE_TEMP_SIZE]

end CPythonListsort

namespace CPythonListsort

/--
[mergeInitTemp_keyed_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeInitStorage.lean)
-/
@[path]
lemma mergeInitTemp_keyed_shape
  {κ : Type u}
  {ν : Type v}
  {listSize : PySSize}
-- given
  (hmax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  let init := mergeInitTemp (κ := κ) (ν := ν) listSize true init.storage.backing = .inline ∧ init.storage.hasValues = true ∧ init.storage.cells.size = min ((listSize.toNat + 1) / 2) 128 := by
-- proof
  simp only [mergeInitTemp, Array.size_replicate, true_and]
  exact mergeInitTempCapacity_keyed_toNat listSize hmax

end CPythonListsort

namespace CPythonListsort

/--
[mergeInitTemp_unkeyed_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeInitStorage.lean)
-/
@[path]
lemma mergeInitTemp_unkeyed_shape
  {κ : Type u}
  {ν : Type v}
  {listSize : PySSize} :
-- imply
  let init := mergeInitTemp (κ := κ) (ν := ν) listSize false init.storage.backing = .inline ∧ init.storage.hasValues = false ∧ init.storage.cells.size = 256 := by
-- proof
  simp [mergeInitTemp, mergeInitTempCapacity, MERGESTATE_TEMP_SIZE]

end CPythonListsort

namespace CPythonListsort

/--
[mergeInitTemp_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeInitStorage.lean)
-/
@[path]
lemma mergeInitTemp_inv
  {κ : Type u}
  {ν : Type v}
  {listSize : PySSize}
-- given
  (hasKeyfunc : Bool)
  (hmax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  TempStorageInv (mergeInitTemp (κ := κ) (ν := ν) listSize hasKeyfunc).storage (mergeInitTemp (κ := κ) (ν := ν) listSize hasKeyfunc).alloced := by
-- proof
  cases hasKeyfunc
  · simp [mergeInitTemp, mergeInitTempCapacity, TempStorageInv,
    TempStorage.multiplier, MERGESTATE_TEMP_SIZE]
  · have hCapacity := mergeInitTempCapacity_keyed_toNat listSize hmax
    simp [mergeInitTemp, TempStorageInv, TempStorage.multiplier, hCapacity,
      MERGESTATE_TEMP_SIZE]
    omega

end CPythonListsort


-- created on 2026-10-23
