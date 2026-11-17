module

public import Theorem.List.ProductCons.eq.FlatMap_FunMapProduct
public import Theorem.List.LengthProductCons.eq.MulLengthS
public import Theorem.Fin.Any_Eq_AddMul.of.Lt_Mul
public import Theorem.List.GetFlatten_AddMul.eq.Get.of.Lt.GtLength.All_EqLength

public section

open List Fin


public theorem List.LengthGetProduct.eq.Length.of.GtLengthProduct
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
    let ⟨i, j, h_ij⟩ := Any_Eq_AddMul.of.Lt_Mul h
    simp [ProductCons.eq.FlatMap_FunMapProduct]
    simp [List.flatMap]
    simp [h_ij]
    rw [GetFlatten_AddMul.eq.Get.of.Lt.GtLength.All_EqLength] <;>
    ·
      simp_all


-- created on 2025-06-12
-- updated on 2025-06-14
