import Lemma.Set.In.is.Any_Eq_Get
import Lemma.Algebra.LengthGetProduct.eq.Length.of.Lt_LengthProduct
open Set Algebra


@[main]
private lemma main
  {s : List (List α)}
-- given
  (h : v ∈ itertools.product s) :
-- imply
  v.length = s.length := by
-- proof
  have h := Any_Eq_Get.of.In h
  let ⟨i, h_i⟩ := h
  rw [h_i]
  simp [LengthGetProduct.eq.Length.of.Lt_LengthProduct]


-- created on 2025-06-29
