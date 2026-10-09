import sympy.Basic


@[path]
private lemma main
  [CommMonoid α]
  {i n : ℕ}
  {f : ℕ → α}
-- given
  (h : i ≤ n) :
-- imply
  ∏ k ∈ Finset.Ico i (n + 1), f k = (∏ k ∈ Finset.Ico i n, f k) * f n := by
-- proof
  exact Finset.prod_Ico_succ_top h f


-- created on 2026-10-02
