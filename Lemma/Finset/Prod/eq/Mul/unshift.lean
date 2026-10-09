import sympy.Basic


@[path]
private lemma main
  [CommGroupWithZero α]
  {f : ℕ → α}
  {a b : ℕ}
-- given
  (h₀ : a < b)
  (h₁ : f a ≠ 0) :
-- imply
  ∏ i ∈ Finset.Ico (a + 1) b, f i = (∏ i ∈ Finset.Ico a b, f i) / f a := by
-- proof
  rw [Finset.prod_eq_prod_Ico_succ_bot h₀]
  exact (mul_div_cancel_left₀ _ h₁).symm


-- created on 2020-03-10
-- updated on 2023-03-30
