import Mathlib
import Def.TateCurve_QShift
import Theorems.Thm_TateCurve_pointX_inv
import Theorems.Thm_TateCurve_pointX_q_mul
import Theorems.Thm_TateCurve_pointX_zpow_mul

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section SymPolynomials

variable (q x₁ x₂ : K)

noncomputable def symSumNum : K :=
  2 * (x₁ * x₂) * (x₁ + x₂) + x₁ * x₂ + 2 * a₄ q * (x₁ + x₂) + 4 * a₆ q

noncomputable def symProdNum : K :=
  (x₁ * x₂) ^ 2 - 2 * a₄ q * (x₁ * x₂) - 4 * a₆ q * (x₁ + x₂) - a₆ q + (a₄ q) ^ 2

end SymPolynomials


section Defects

variable [CompleteSpace K] {q u v w : K}


variable (q u v)

noncomputable def addDefectSum : K :=
  (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 -
    symSumNum q (pointX q u) (pointX q v)

noncomputable def addDefectProd : K :=
  pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 -
    symProdNum q (pointX q u) (pointX q v)

end Defects

end TateCurve

set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


section BoundedDescent

variable (c : ℕ → ℕ → K)

noncomputable def specTail (w : K) (M : ℕ) : K :=
  ∑' k : ℕ, if 1 ≤ k then c (M + k) k * w⁻¹ ^ k else 0

noncomputable def specAlpha (w : K) (M : ℕ) : K :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal M).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1), c p.1 p.2 * w ^ p.2

noncomputable def specGamma (M : ℕ) : K :=
  ∑ k ∈ Finset.Icc 1 M, (-2 : K) * c M k

end BoundedDescent

end TateCurve
