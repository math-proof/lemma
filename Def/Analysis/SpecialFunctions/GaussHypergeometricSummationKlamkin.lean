/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GaussHypergeometricSummationKlamkin.lean -/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Gauss hypergeometric summation of Klamkin

The first Gamma quotient from U. Abel, "A Short Proof of the Binomial
Identities of Frisch and Klamkin," _Journal of Integer Sequences_ 23 (2020),
Article 20.7.1: `₂F₁(n, b + 1; b - a; 1)` equals a quotient of Gamma values.
-/


namespace MetaMathlibExt

section

/-- Coefficient shorthand: the k-th term of ₂F₁(j, b+1; b-a) at x = 1. -/
noncomputable def klamCoeff (b a : ℝ) (m k : ℕ) : ℝ :=
  ordinaryHypergeometricCoefficient ((m : ℕ) : ℝ) (b + 1) (b - a) k

noncomputable def klamF (b a : ℝ) (m : ℕ) : ℝ :=
  ∑' k, klamCoeff b a m k

noncomputable def klamG (a b : ℝ) (m : ℕ) : ℝ :=
  Real.Gamma (-a - 1 - ((m : ℕ) : ℝ)) * Real.Gamma (b - a) /
    (Real.Gamma (b - a - ((m : ℕ) : ℝ)) * Real.Gamma (-a - 1))

end
end MetaMathlibExt
