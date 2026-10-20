import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Polynomial.MomentGeneratingJFraction
open MetaMathlibExt


/--
[moment_generating_function_as_J_fraction_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/MomentGeneratingJFraction.lean)
-/
@[path]
private lemma moment_generating_function_as_J_fraction_general_eq
  {p : ℕ → Polynomial ℝ}
  {L : Polynomial ℝ →ₗ[ℝ] ℝ}
  {α β μ : ℕ → ℝ}
-- given
  (h0 : p 0 = 1)
  (h1 : p 1 = Polynomial.X - Polynomial.C (α 0))
  (hrec : ∀ n : ℕ, 1 ≤ n → p (n + 1) = (Polynomial.X - Polynomial.C (α n)) * p n - Polynomial.C (β n) * p (n - 1))
  (hμ : ∀ k : ℕ, μ k = L (Polynomial.X ^ k))
  (hLp : ∀ n : ℕ, 1 ≤ n → L (p n) = 0) :
-- imply
  ∃ S : ℕ → PowerSeries ℝ,
    (∀ n : ℕ, PowerSeries.constantCoeff (S n) = 1) ∧ HasJacobiFraction μ α β (μ 0) S := by
-- proof
  apply MetaMathlibExt.moment_generating_function_as_J_fraction_general p L α β μ h0 h1 hrec hμ hLp

/--
[moment_generating_function_as_J_fraction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/MomentGeneratingJFraction.lean)
-/
@[path]
private lemma moment_generating_function_as_J_fraction_eq
  {p : ℕ → Polynomial ℝ}
  {L : Polynomial ℝ →ₗ[ℝ] ℝ}
  {α β μ : ℕ → ℝ}
  {g : PowerSeries ℝ} :
-- imply
  (∀ n : ℕ, (p n).Monic ∧ (p n).natDegree = n) →
    (p 0 = 1) →
    (p 1 = Polynomial.X - Polynomial.C (α 0)) →
    (∀ n : ℕ, 1 ≤ n → p (n + 1) = (Polynomial.X - Polynomial.C (α n)) * p n - Polynomial.C (β n) * p
    (n - 1)) →
    (∀ n : ℕ, 1 ≤ n → β n ≠ 0) →
    (∀ m n : ℕ, m ≠ n → L (p m * p n) = 0) →
    (∀ n : ℕ, L (p n * p n) ≠ 0) →
    (∀ k : ℕ, μ k = L (Polynomial.X ^ k)) →
    (μ 0 ≠ 0) →
    (g = PowerSeries.mk μ) →
    ∃ S : ℕ → PowerSeries ℝ,
    (∀ n : ℕ, PowerSeries.constantCoeff (S n) = 1) ∧
    (g = PowerSeries.C (μ 0) * S 0) ∧
    ∀ n : ℕ, S n *
    (1 - PowerSeries.C (α n) * PowerSeries.X - PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * S
    (n + 1)) = 1 := by
-- proof
  apply MetaMathlibExt.moment_generating_function_as_J_fraction p L α β μ g


-- created on 2026-10-20
