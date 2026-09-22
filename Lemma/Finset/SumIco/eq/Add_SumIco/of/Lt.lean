import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid α]
  {a b : ℕ}
  {f : ℕ → α}
-- given
  (h : a < b) :
-- imply
  ∑ k ∈ Finset.Ico a b, f k = f a + ∑ k ∈ Finset.Ico (a + 1) b, f k :=
-- proof
  Finset.sum_eq_sum_Ico_succ_bot h _


-- created on 2020-03-23
