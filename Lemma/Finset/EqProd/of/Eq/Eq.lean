import sympy.sets.sets
import sympy.Basic


@[main]
private lemma push
  {a b : ℕ}
  {g f : ℕ → ℤ}
-- given
  (h : a ≤ b)
  (h₀ : g b = f b)
  (h₁ : ∏ k ∈ Finset.Ico a b, g k = ∏ k ∈ Finset.Ico a b, f k) :
-- imply
  ∏ k ∈ Finset.Ico a (b + 1), g k = ∏ k ∈ Finset.Ico a (b + 1), f k := by
-- proof
  rw [Finset.prod_Ico_succ_top h, Finset.prod_Ico_succ_top h, h₀, h₁]


@[main]
private lemma unshift
  {a b : ℕ}
  {g f : ℕ → ℤ}
-- given
  (h : a < b)
  (h₀ : g a = f a)
  (h₁ : ∏ k ∈ Finset.Ico (a + 1) b, g k = ∏ k ∈ Finset.Ico (a + 1) b, f k) :
-- imply
  ∏ k ∈ Finset.Ico a b, g k = ∏ k ∈ Finset.Ico a b, f k := by
-- proof
  rw [Finset.prod_eq_prod_Ico_succ_bot h, Finset.prod_eq_prod_Ico_succ_bot h, h₀, h₁]


-- created on 2026-09-27
