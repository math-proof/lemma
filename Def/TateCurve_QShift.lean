import Mathlib
import Def.TateCurve_DefectLines

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter


open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


section Coefficients

variable (u : K)

noncomputable def qshiftAlpha (M : ℕ) : K :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal M).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1),
    ((lineCoeff p.1 p.2 : ℤ) : K) * u ^ p.2

noncomputable def qshiftBeta (M : ℕ) : K :=
  ∑' k : ℕ, if 1 ≤ k then ((lineCoeff (M + k) k : ℤ) : K) * u⁻¹ ^ k else 0

noncomputable def qshiftGamma (M : ℕ) : K :=
  ∑ k ∈ Finset.Icc 1 M, (-2 : K) * ((lineCoeff M k : ℤ) : K)

end Coefficients

end TateCurve

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]


section Reindex

def shiftPair : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)

end Reindex

section Families

variable (u q : K)

noncomputable def hubTerm (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    ((lineCoeff p.1 p.2 : ℤ) : K) * Fz (q * u) (p.2 : ℤ) * q ^ p.1 else 0

noncomputable def alphaTerm (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    ((lineCoeff p.1 p.2 : ℤ) : K) * u ^ p.2 * q ^ (p.1 + p.2) else 0

noncomputable def betaTerm (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    ((lineCoeff p.1 p.2 : ℤ) : K) * u⁻¹ ^ p.2 * q ^ (p.1 - p.2) else 0

noncomputable def gammaTerm (p : ℕ × ℕ) : K :=
  if 1 ≤ p.2 ∧ p.2 ≤ p.1 then
    (-2 : K) * ((lineCoeff p.1 p.2 : ℤ) : K) * q ^ p.1 else 0

end Families

end TateCurve
