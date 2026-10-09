import sympy.sets.sets
import sympy.Basic


@[path]
private lemma push
  {a b : ℕ}
  {g f : ℕ → ℤ}
-- given
  (h : a ≤ b)
  (h₀ : g b < f b)
  (h₁ : ∑ k ∈ Finset.Ico a b, g k < ∑ k ∈ Finset.Ico a b, f k) :
-- imply
  ∑ k ∈ Finset.Ico a (b + 1), g k < ∑ k ∈ Finset.Ico a (b + 1), f k := by
-- proof
  rw [Finset.sum_Ico_succ_top h, Finset.sum_Ico_succ_top h]
  exact add_lt_add h₁ h₀


@[path]
private lemma unshift
  {a b : ℕ}
  {g f : ℕ → ℤ}
-- given
  (h : a < b)
  (h₀ : g a < f a)
  (h₁ : ∑ k ∈ Finset.Ico (a + 1) b, g k < ∑ k ∈ Finset.Ico (a + 1) b, f k) :
-- imply
  ∑ k ∈ Finset.Ico a b, g k < ∑ k ∈ Finset.Ico a b, f k := by
-- proof
  rw [Finset.sum_eq_sum_Ico_succ_bot h, Finset.sum_eq_sum_Ico_succ_bot h]
  exact add_lt_add h₀ h₁


-- created on 2019-09-30
