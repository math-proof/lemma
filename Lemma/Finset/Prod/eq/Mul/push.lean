import sympy.Basic


@[path]
private lemma main
  [CommGroupWithZero α]
  {f : ℕ → α}
  {a b : ℕ}
-- given
  (h₀ : a ≤ b)
  (h₁ : f b ≠ 0) :
-- imply
  ∏ i ∈ Finset.Ico a b, f i = (∏ i ∈ Finset.Ico a (b + 1), f i) / f b := by
-- proof
  rw [Nat.Ico_succ_right_eq_insert_Ico h₀, Finset.prod_insert (by simp)]
  exact (mul_div_cancel_left₀ _ h₁).symm


-- created on 2020-03-09
