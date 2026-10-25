/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RiordanOrthogonalPolynomials.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Def.Algebra.Polynomial.FormalOrthogonality
import Def.LinearAlgebra.Matrix.StieltjesMatrix
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse
import Lemma.Int.Polynomial.FavardIff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination


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
