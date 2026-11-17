/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RiordanOrthogonalPolynomials.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Def.Algebra.Polynomial.FormalOrthogonality
public import Def.LinearAlgebra.Matrix.StieltjesMatrix
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

@[expose] public section

section

namespace MetaMathlibExt

/-- Polynomial with row `n` of `L` as coefficients. -/
noncomputable def polyOfRow (L : ℕ → ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (L n k)

/-- Inverse array defined by the Stieltjes production recurrence. -/
noncomputable def linvOf (r₁ s₁ r s : ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => ∑ j ∈ Finset.range (n + 2),
      linvOf r₁ s₁ r s n j * stieltjesMatrix r₁ s₁ r s j k

end MetaMathlibExt
end
