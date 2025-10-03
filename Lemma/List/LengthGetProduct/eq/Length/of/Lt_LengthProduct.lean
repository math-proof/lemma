import stdlib.List
import Lemma.List.ProductCons.eq.FlatMapFunMapProduct
import Lemma.List.LengthProductCons.eq.MulLengthS
import Lemma.Algebra.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.GetFlatten_AddMul.eq.Get.of.Lt.Lt_Length.All_EqLength
open Algebra List


@[main]
private lemma main
  {s : List (List α)}
-- given
  (h : i < (itertools.product s).length) :
-- imply
  (itertools.product s)[i].length = s.length := by
-- proof
  induction s generalizing i with
  | nil =>
    unfold itertools.product
    simp_all
  | cons x xs ih =>
    rw [LengthProductCons.eq.MulLengthS] at h
    let ⟨i, hi, j, hj, h_ij⟩ := Any_Eq_AddMul.of.Lt_Mul h
    simp [ProductCons.eq.FlatMapFunMapProduct]
    simp [List.flatMap]
    simp [h_ij]
    rw [GetFlatten_AddMul.eq.Get.of.Lt.Lt_Length.All_EqLength] <;>
    ·
      simp_all


-- created on 2025-06-12
-- updated on 2025-06-14
