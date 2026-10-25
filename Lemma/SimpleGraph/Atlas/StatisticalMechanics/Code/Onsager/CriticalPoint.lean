import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CriticalPoint
open StatMech StatMech.Onsager


/--
[ons_sq_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean)
-/
@[path]
private lemma ons_sq_identity_eq
  {β : ℝ} :
-- imply
  Real.cosh (2*β)^2 - 2 * Real.sinh (2*β) = (Real.sinh (2*β) - 1)^2 := by
-- proof
  apply StatMech.Onsager.ons_sq_identity β

/--
[ons_gInt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean)
-/
@[path]
private lemma ons_gInt_zero_eq
  {β : ℝ} :
-- imply
  ons_gInt β 0 0 = (Real.sinh (2*β) - 1)^2 := by
-- proof
  apply StatMech.Onsager.ons_gInt_zero β

/--
[ons_gInt_nonneg_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean)
-/
@[path]
private lemma ons_gInt_nonneg_at_zero_eq
  {β : ℝ} :
-- imply
  0 ≤ ons_gInt β 0 0 := by
-- proof
  apply StatMech.Onsager.ons_gInt_nonneg_at_zero β

/--
[ons_gInt_min](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean)
-/
@[path]
private lemma ons_gInt_min_eq
  {β k₁ k₂ : ℝ}
-- given
  (hβ : 0 ≤ β) :
-- imply
  ons_gInt β 0 0 ≤ ons_gInt β k₁ k₂ := by
-- proof
  apply StatMech.Onsager.ons_gInt_min β k₁ k₂ hβ

/--
[ons_gInt_zero_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean)
-/
@[path]
private lemma ons_gInt_zero_eq_zero_iff_eq
  {β : ℝ} :
-- imply
  ons_gInt β 0 0 = 0 ↔ Real.sinh (2*β) = 1 := by
-- proof
  apply StatMech.Onsager.ons_gInt_zero_eq_zero_iff β

/--
[ons_betaC_sinh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean)
-/
@[path]
private lemma ons_betaC_sinh_eq :
-- imply
  Real.sinh (2 * ons_betaC) = 1 := by
-- proof
  apply StatMech.Onsager.ons_betaC_sinh

/--
[ons_betaC_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean)
-/
@[path]
private lemma ons_betaC_pos_eq :
-- imply
  0 < ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_betaC_pos

/--
[ons_betaC_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalPoint.lean)
-/
@[path]
private lemma ons_betaC_unique_eq
  {β : ℝ}
-- given
  (hβ : 0 < β) :
-- imply
  Real.sinh (2*β) = 1 ↔ β = ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_betaC_unique β hβ


-- created on 2026-10-23
