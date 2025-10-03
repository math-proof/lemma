import Lemma.Vector.ValGet.eq.ValArraySliceFlatten
import Lemma.List.LengthArraySlice.eq.Min_SubLength
import Lemma.List.LengthFlatten.eq.SumMapLength
import Lemma.Algebra.SumMapVal.eq.Mul
import Lemma.Algebra.GetVal.eq.Get
import Lemma.Algebra.GetVal.eq.Get.of.Lt
import Lemma.Algebra.Ge.of.NotLt
import Lemma.List.GetElem!.eq.None.of.Ge_Length
import Lemma.List.EqGetS.of.Eq.Lt_Length
open Algebra Vector List


@[main]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m) :
-- imply
  v[i].val = (v.toList.map List.Vector.toList).flatten.array_slice (i * n) n := by
-- proof
  have h := ValGet.eq.ValArraySliceFlatten v i
  ext j t
  by_cases h_j : j < v[i].val.length
  ·
    let h_lt := h_j
    simp at h_lt
    by_cases h_j' : j < (v.flatten.array_slice (i * n) n).val.length
    ·
      have h := EqGetS.of.Eq.Lt_Length h_j h
      simp at h_j'
      have h_j : j < ((List.map List.Vector.toList v.toList).flatten.array_slice (i * n) n).length := by
        simp_all
        rw [LengthArraySlice.eq.Min_SubLength]
        rw [LengthFlatten.eq.SumMapLength]
        simp_all
        simp [List.Vector.toList]
        rw [SumMapVal.eq.Mul]
        exact h_j'.right
      simp [h_lt, h_j]
      rw [GetVal.eq.Get.of.Lt]
      ·
        unfold List.Vector.array_slice List.Vector.drop List.Vector.take at h
        unfold List.Vector.flatten at h
        simp at h
        rw [GetVal.eq.Get.of.Lt] at h
        ·
          constructor <;>
          ·
            intro h_ij
            rw [← h_ij]
            unfold List.array_slice
            simp
            rw [← h]
      ·
        assumption
    ·
      have h_j := Ge.of.NotLt h_j'
      simp_all
  ·
    have h_j := Ge.of.NotLt h_j
    simp at h_j
    have h_ge : j ≥ v[i.val].val.length := by
      simp_all
    simp
    rw [GetElem!.eq.None.of.Ge_Length h_ge]
    simp
    have h_ge : j ≥ ((List.map List.Vector.toList v.toList).flatten.array_slice (↑i * n) n).length := by
      rw [LengthArraySlice.eq.Min_SubLength]
      simp_all
    rw [GetElem!.eq.None.of.Ge_Length h_ge]
    simp


-- created on 2025-05-27
-- updated on 2025-05-31
