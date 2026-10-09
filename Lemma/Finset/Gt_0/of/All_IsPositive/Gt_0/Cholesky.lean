import sympy.Basic
open scoped ComplexOrder


@[path]
private lemma main
  {n : ℕ}
  {t : Fin n}
  {A L : Matrix (Fin n) (Fin n) ℂ}
  {ξ : Fin n → ℂ}
-- given
  (_h₀ : ∀ i, i < t → 0 < L i i)
  (_h₁ : 0 < A t t + ((∑ i ∈ Finset.Iio t, (‖ξ i‖ ^ 2 * ∑ k ∈ Finset.Iic i, ‖L i k‖ ^ 2 + 2 * RCLike.re (star (ξ i) * ∑ j ∈ Finset.Ioc i t, (if j = t then 1 else ξ j) * ∑ k ∈ Finset.Iic i, star (L j k) * L i k)) : ℝ) : ℂ)) :
-- imply
  ((∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 : ℝ) : ℂ) < A t t := by
-- proof
  -- sorry: false as stated in py (ξ is a free symbol; py's proof relies on a specific ξ that the statement does not fix).
  -- Counterexample t = 1, ξ = 0: the hypothesis reduces to 0 < A 1 1 and the conclusion to ‖L 1 0‖² < A 1 1,
  -- which fails for A 1 1 = 1, L 1 0 = 2 (nothing else constrains L 1 0)
  sorry


@[path]
private lemma real
  {n : ℕ}
  {t : Fin n}
  {A L : Matrix (Fin n) (Fin n) ℝ}
  {ξ : Fin n → ℝ}
-- given
  (_h₀ : ∀ i, i < t → 0 < L i i)
  (_h₁ : 0 < A t t + ∑ i ∈ Finset.Iio t, (ξ i ^ 2 * ∑ k ∈ Finset.Iic i, L i k ^ 2 + 2 * ξ i * ∑ j ∈ Finset.Ioc i t, (if j = t then 1 else ξ j) * ∑ k ∈ Finset.Iic i, L j k * L i k)) :
-- imply
  ∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 < A t t := by
-- proof
  -- sorry: false as stated in py (ξ is a free symbol; py's proof relies on a specific ξ that the statement does not fix).
  -- Counterexample t = 1, ξ = 0: the hypothesis reduces to 0 < A 1 1 and the conclusion to ‖L 1 0‖² < A 1 1,
  -- which fails for A 1 1 = 1, L 1 0 = 2 (nothing else constrains L 1 0)
  sorry


-- created on 2023-06-22
