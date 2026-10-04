import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid α]
  {f : ℕ → α}
  {i n : ℕ}
-- given
  (h : i < n) :
-- imply
  ∑ k ∈ Finset.Ico (i + 1) n, f k + f i = ∑ k ∈ Finset.Ico i n, f k := by
-- proof
  rw [Finset.sum_eq_sum_Ico_succ_bot h]
  exact add_comm _ _


-- created on 2018-08-08
