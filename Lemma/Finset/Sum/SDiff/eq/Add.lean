import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A B : Finset ℤ}
  {f : ℤ → ℝ} :
-- imply
  ∑ x ∈ A \ B, f x = ∑ x ∈ A, f x - ∑ x ∈ A ∩ B, f x := by
-- proof
  rw [← Finset.sum_sdiff (Finset.inter_subset_left : A ∩ B ⊆ A), Finset.sdiff_inter_self_left]
  ring


-- created on 2020-03-23
