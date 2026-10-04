import sympy.Basic


@[main]
private lemma main
  [CommSemiring α]
  {a : α}
  {f : ℕ → α}
  {i n : ℕ} :
-- imply
  a ^ n * ∏ k ∈ Finset.Ico i (n + i), f k = ∏ k ∈ Finset.Ico i (n + i), f k * a := by
-- proof
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel_right]
  exact mul_comm _ _


-- created on 2023-08-20
