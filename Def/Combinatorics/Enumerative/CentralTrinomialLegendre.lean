/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralTrinomialLegendre.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Def.NumberTheory.TrinomialCoefficient
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Central trinomial coefficients and Legendre polynomials

This file proves that each central trinomial coefficient is a special value of a Legendre
polynomial.
-/


section

namespace MetaMathlibExt

/-- Evaluation point for the Legendre side: `(1 + i/√3)/2`. -/
noncomputable def legPt : ℂ := (1 + Complex.I / (Real.sqrt 3 : ℂ)) / 2

/-- The shifted Legendre value at `legPt`. -/
noncomputable def legVal (n : ℕ) : ℂ :=
  Polynomial.aeval legPt (Polynomial.shiftedLegendre n)

/-- The Legendre side of the identity as a sequence. -/
noncomputable def legSeq (n : ℕ) : ℂ :=
  Complex.I ^ n * (Real.sqrt ((3 : ℝ) ^ n) : ℂ) * legVal n

/-- The central trinomial coefficient as a complex sequence. -/
noncomputable def triSeq (n : ℕ) : ℂ :=
  (trinomialCoefficient n n : ℂ)

end MetaMathlibExt
end
