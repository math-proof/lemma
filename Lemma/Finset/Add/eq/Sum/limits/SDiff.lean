import sympy.Basic


@[main]
private lemma main
  [DecidableEq α] [AddCommGroup β]
  {A B : Finset α}
  {f : α → β} :
-- imply
  ∑ k ∈ A, f k - ∑ k ∈ A ∩ B, f k = ∑ k ∈ A \ B, f k := by
-- proof
  rw [← Finset.sum_sdiff (Finset.inter_subset_left : A ∩ B ⊆ A), Finset.sdiff_inter_self_left]
  abel


-- created on 2026-09-27
