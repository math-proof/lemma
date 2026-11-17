module

public import Theorem.Set.In.is.Any_Eq_Get
public import Theorem.Bool.UFn.of.Eq
public import Theorem.List.LengthGetProduct.eq.Length.of.GtLengthProduct

public section

open Set List Bool


public theorem List.Length.of.In_CartesianProduct
  {x s : List ℕ}
-- given
  (h : x ∈ s.cartesianProduct) :
-- imply
  x.length = s.length := by
-- proof
  unfold List.cartesianProduct at h
  let ⟨i, h⟩ := Any_Eq_Get.of.In h
  have h := UFn.of.Eq h List.length
  rw [h]
  have hi := i.isLt
  have := LengthGetProduct.eq.Length.of.GtLengthProduct hi
  simp at this
  rw [← this]
  simp_all


-- created on 2025-06-14
