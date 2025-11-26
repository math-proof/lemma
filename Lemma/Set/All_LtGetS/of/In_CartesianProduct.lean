import Lemma.Set.In.is.Any_Eq_Get
import Lemma.List.GetCartesianProduct.lt.Get.of.GtLength.Lt_LengthCartesianProduct
open Set List


@[main]
private lemma main
  {x s : List ℕ}
-- given
  (h : x ∈ s.cartesianProduct) :
-- imply
  ∀ i (h_x : i < x.length) (h_s : i < s.length), x[i] < s[i] := by
-- proof
  intro i h_x h_s
  let ⟨j, h⟩ := Any_Eq_Get.of.In h
  have h_j := j.isLt
  have h_i : i < s.cartesianProduct[j].length := by rwa [← h]
  simp_all [GetCartesianProduct.lt.Get.of.GtLength.Lt_LengthCartesianProduct h_j h_s]


-- created on 2025-06-14
