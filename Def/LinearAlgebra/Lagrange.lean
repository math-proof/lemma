/-
# Evaluated Lagrange basis and Lebesgue function

Shared evaluated-basis wrapper around Mathlib's `Lagrange.basis`, plus the
Lebesgue function and Lagrange interpolant built from it.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

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
