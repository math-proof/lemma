/-
# Evaluated Lagrange basis and Lebesgue function

Shared evaluated-basis wrapper around Mathlib's `Lagrange.basis`, plus the
Lebesgue function and Lagrange interpolant built from it.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Lagrange


namespace Lagrange

variable {n : ℕ} (x : Fin n → ℝ)

/-- Lagrange fundamental polynomial `l_k(t)` for nodes `x`, via Mathlib's
`Lagrange.basis` evaluated at `t`. -/
noncomputable def evalBasis (k : Fin n) (t : ℝ) : ℝ :=
  Polynomial.eval t (Lagrange.basis Finset.univ x k)

/-- Lebesgue function `Lₙ(t) = ∑_k |l_k(t)|`. -/
noncomputable def lebesgueFunction (t : ℝ) : ℝ :=
  ∑ k : Fin n, |Lagrange.evalBasis x k t|

/-- Lagrange interpolant `𝓛ⁿf(t) = ∑ₖ f(xₖ) * lₖ(t)`. -/
noncomputable def evalInterpolant (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ k : Fin n, f (x k) * Lagrange.evalBasis x k t

end Lagrange
