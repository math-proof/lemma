import sympy.sets.sets
import sympy.Basic


@[main]
private lemma push
  {a b : ℕ}
  {g f : ℕ → ℤ}
-- given
  (hg : ∀ k, g k ≥ 0)
  (h : a ≤ b)
  (h₀ : g b ≤ f b)
  (h₁ : ∏ k ∈ Finset.Ico a b, g k ≤ ∏ k ∈ Finset.Ico a b, f k) :
-- imply
  ∏ k ∈ Finset.Ico a (b + 1), g k ≤ ∏ k ∈ Finset.Ico a (b + 1), f k := by
-- proof
  rw [Finset.prod_Ico_succ_top h, Finset.prod_Ico_succ_top h]
  exact mul_le_mul h₁ h₀ (hg b) (le_trans (Finset.prod_nonneg (fun k _ => hg k)) h₁)


@[main]
private lemma unshift
  {a b : ℕ}
  {g f : ℕ → ℤ}
-- given
  (hg : ∀ k, g k ≥ 0)
  (h : a < b)
  (h₀ : g a ≤ f a)
  (h₁ : ∏ k ∈ Finset.Ico (a + 1) b, g k ≤ ∏ k ∈ Finset.Ico (a + 1) b, f k) :
-- imply
  ∏ k ∈ Finset.Ico a b, g k ≤ ∏ k ∈ Finset.Ico a b, f k := by
-- proof
  rw [Finset.prod_eq_prod_Ico_succ_bot h, Finset.prod_eq_prod_Ico_succ_bot h]
  exact mul_le_mul h₀ h₁ (Finset.prod_nonneg (fun k _ => hg k)) (le_trans (hg a) h₀)


-- created on 2026-09-27
