import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid α]
  {a b : ℕ}
  {f : ℕ → α}
-- given
  (h : a ≤ b) :
-- imply
  ∑ k ∈ Finset.Ico a (b + 1), f k = ∑ k ∈ Finset.Ico a b, f k + f b := by
-- proof
  apply Finset.sum_Ico_succ_top h


-- created on 2019-04-26
-- updated on 2026-09-07
