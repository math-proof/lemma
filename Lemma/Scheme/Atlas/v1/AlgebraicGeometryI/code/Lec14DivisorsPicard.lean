import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec14DivisorsPicard.Part2
open AlgebraicGeometry CategoryTheory Lec14DivisorsPicard
open scoped nonZeroDivisors
open LocallyFactorialDivisors
open IsDedekindDomain
open InvertibleSheaves


namespace Lec14DivisorsPicard

/--
[degree_eq_of_linearlyEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14DivisorsPicard.lean)
-/
@[path]
lemma degree_eq_of_linearlyEquiv
  [DecidableEq Y]
  {D₁ D₂ : WeilDivisor.Group Y}
-- given
  (IsPrincipal : WeilDivisor.Group Y → Prop)
  (h_princ_deg : ∀ P, IsPrincipal P → weilDivisorDegree P = 0)
  (h_equiv : IsPrincipal (D₁ - D₂)) :
-- imply
  weilDivisorDegree D₁ = weilDivisorDegree D₂ := by
-- proof
  have h := h_princ_deg _ h_equiv
  have hsub : D₁ - D₂ = D₁ + (-D₂) := sub_eq_add_neg D₁ D₂
  rw [hsub, weilDivisorDegree_add] at h
  have hneg : weilDivisorDegree (-D₂) = -weilDivisorDegree D₂ := by
    simp only [weilDivisorDegree]
    rw [Finsupp.sum_neg_index (by simp)]
    simp [Finsupp.sum, Finset.sum_neg_distrib]
  linarith

end Lec14DivisorsPicard

/--
[weilDivisorDegree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14DivisorsPicard.lean)
-/
@[path]
private lemma weilDivisorDegree_zero_eq
  [DecidableEq Y] :
-- imply
  weilDivisorDegree (0 : WeilDivisor.Group Y) = 0 := by
-- proof
  apply Lec14DivisorsPicard.weilDivisorDegree_zero

/--
[weilDivisorDegree_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14DivisorsPicard.lean)
-/
@[path]
private lemma weilDivisorDegree_add_eq
  [DecidableEq Y]
  {D₁ D₂ : WeilDivisor.Group Y} :
-- imply
  weilDivisorDegree (D₁ + D₂) = weilDivisorDegree D₁ + weilDivisorDegree D₂ := by
-- proof
  apply Lec14DivisorsPicard.weilDivisorDegree_add D₁ D₂


-- created on 2026-10-23
