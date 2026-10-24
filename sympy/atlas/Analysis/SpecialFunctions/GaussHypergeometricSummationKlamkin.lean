/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GaussHypergeometricSummationKlamkin.lean -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gauss hypergeometric summation of Klamkin

The first Gamma quotient from U. Abel, "A Short Proof of the Binomial
Identities of Frisch and Klamkin," _Journal of Integer Sequences_ 23 (2020),
Article 20.7.1: `₂F₁(n, b + 1; b - a; 1)` equals a quotient of Gamma values.
-/

namespace MetaMathlibExt

section

/-- Coefficient shorthand: the k-th term of ₂F₁(j, b+1; b-a) at x = 1. -/
private noncomputable def klamCoeff (b a : ℝ) (m k : ℕ) : ℝ :=
  ordinaryHypergeometricCoefficient ((m : ℕ) : ℝ) (b + 1) (b - a) k

private noncomputable def klamF (b a : ℝ) (m : ℕ) : ℝ :=
  ∑' k, klamCoeff b a m k

private noncomputable def klamG (a b : ℝ) (m : ℕ) : ℝ :=
  Real.Gamma (-a - 1 - ((m : ℕ) : ℝ)) * Real.Gamma (b - a) /
    (Real.Gamma (b - a - ((m : ℕ) : ℝ)) * Real.Gamma (-a - 1))
end
end MetaMathlibExt
