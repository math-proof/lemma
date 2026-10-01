import sympy.Basic


@[main]
private lemma main
  [CommMonoid α]
  {a b : ℕ}
  {f : ℕ → α}
-- given
  (h : a ≤ b) :
-- imply
  (∏ k ∈ Finset.Ico a b, f k) * f b = ∏ k ∈ Finset.Ico a (b + 1), f k := by
-- proof
  exact (Finset.prod_Ico_succ_top h f).symm


-- created on 2026-10-01
