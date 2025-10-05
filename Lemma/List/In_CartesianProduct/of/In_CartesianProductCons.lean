import Lemma.Set.In_CartesianProduct.is.EqLengthS.All_LtGetS
import Lemma.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
open Set List


@[main]
private lemma main
  {x₀ s₀ : ℕ}
  {x s : List ℕ}
-- given
  (h : (x₀ :: x) ∈ (s₀ :: s).cartesianProduct) :
-- imply
  x ∈ s.cartesianProduct := by
-- proof
  let ⟨h_eq, h_all⟩ := EqLengthS.All_LtGetS.of.In_CartesianProduct h
  apply In_CartesianProduct.of.EqLengthS.All_LtGetS
  ·
    simp at h_eq
    assumption
  ·
    intro i h_x h_s
    have h := h_all (i + 1) (by simp_all) (by simp_all)
    simp_all


-- created on 2025-06-14
