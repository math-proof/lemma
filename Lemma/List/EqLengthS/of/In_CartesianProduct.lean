import Lemma.Set.In.is.Any_Eq_Get
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.Algebra.LtVal
import Lemma.List.LengthGetProduct.eq.Length.of.Lt_LengthProduct
open Set Algebra List Bool


@[main]
private lemma main
  {x s : List ℕ}
-- given
  (h : x ∈ s.cartesianProduct) :
-- imply
  x.length = s.length := by
-- proof
  unfold List.cartesianProduct at h
  let ⟨i, h⟩ := Any_Eq_Get.of.In h
  have h := EqUFnS.of.Eq h List.length
  rw [h]
  have hi := LtVal i
  have := LengthGetProduct.eq.Length.of.Lt_LengthProduct hi
  simp at this
  rw [← this]
  simp_all


-- created on 2025-06-14
