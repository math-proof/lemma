import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A B : Finset ℤ}
  {f : ℤ → ℤ} :
-- imply
  (∏ k ∈ A \ B, f k) * ∏ k ∈ A ∩ B, f k = ∏ k ∈ A, f k := by
-- proof
  rw [← Finset.sdiff_inter_self_left]
  exact Finset.prod_sdiff Finset.inter_subset_left


-- created on 2026-09-27
