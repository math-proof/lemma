import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingGeneralSymbol
open MeasureTheory StatMech StatMech.FrontierA


/--
[triangularIsingSymbol_eq_innerSinusoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingSymbol_eq_innerSinusoid_eq
  {J1 J2 J3 k1 k2 : Real} :
-- imply
  triangularIsingSymbol J1 J2 J3 k1 k2 = triangularIsingInnerA J1 J2 J3 k1 - triangularIsingInnerU J2 J3 k1 * Real.cos k2 - triangularIsingInnerV J3 k1 * Real.sin k2 := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_eq_innerSinusoid J1 J2 J3 k1 k2

/--
[triangularIsingInnerA_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingInnerA_pos_eq
  {J1 J2 J3 k1 : Real} :
-- imply
  0 < triangularIsingInnerA J1 J2 J3 k1 := by
-- proof
  apply StatMech.FrontierA.triangularIsingInnerA_pos J1 J2 J3 k1

/--
[triangularIsingInner_discriminant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingInner_discriminant_nonneg_eq
  {J1 J2 J3 k1 : Real} :
-- imply
  0 ≤ triangularIsingInnerA J1 J2 J3 k1 ^ 2 - (triangularIsingInnerU J2 J3 k1 ^ 2 + triangularIsingInnerV J3 k1 ^ 2) := by
-- proof
  apply StatMech.FrontierA.triangularIsingInner_discriminant_nonneg J1 J2 J3 k1

/--
[triangularIsingSymbol_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingSymbol_nonneg_eq
  {J1 J2 J3 k1 k2 : Real} :
-- imply
  0 ≤ triangularIsingSymbol J1 J2 J3 k1 k2 := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_nonneg J1 J2 J3 k1 k2

/--
[integral_log_triangularIsingSymbol_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma integral_log_triangularIsingSymbol_inner_eq
  {J1 J2 J3 k1 : Real} :
-- imply
  (∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) = 2 * Real.pi * Real.log (nonnegativeSinusoidQ (triangularIsingInnerA J1 J2 J3 k1) (triangularIsingInnerU J2 J3 k1) (triangularIsingInnerV J3 k1) / 2) := by
-- proof
  apply StatMech.FrontierA.integral_log_triangularIsingSymbol_inner J1 J2 J3 k1

/--
[continuous_triangularIsingFreeEnergyValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma continuous_triangularIsingFreeEnergyValue_eq :
-- imply
  Continuous (fun J : Real × Real × Real => triangularIsingFreeEnergyValue J.1 J.2.1 J.2.2) := by
-- proof
  apply StatMech.FrontierA.continuous_triangularIsingFreeEnergyValue

/--
[triangularIsingHighTempSymbol_corner_eq_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingHighTempSymbol_corner_eq_sq_eq
  {J1 J2 J3 : Real}
  {e1 e2 : Fin 2} :
-- imply
  triangularIsingHighTempSymbol J1 J2 J3 (triangularIsingCornerMomentum e1) (triangularIsingCornerMomentum e2) = triangularIsingCornerFactor e1 e2 (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) ^ 2 := by
-- proof
  apply StatMech.FrontierA.triangularIsingHighTempSymbol_corner_eq_sq J1 J2 J3 e1 e2

/--
[triangularIsingCornerFactor_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingCornerFactor_affine_eq
  {e1 e2 : Fin 2}
  {t1 t2 t3 : Real} :
-- imply
  triangularIsingCornerFactor e1 e2 t1 t2 t3 = triangularIsingCornerFactorConst e1 e2 t2 t3 + t1 * triangularIsingCornerFactorCoeff e1 e2 t2 t3 := by
-- proof
  apply StatMech.FrontierA.triangularIsingCornerFactor_affine e1 e2 t1 t2 t3

/--
[triangularIsingCornerFactor_const_coeff_not_both_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingCornerFactor_const_coeff_not_both_zero_eq
  {e1 e2 : Fin 2}
  {t2 t3 : Real} :
-- imply
  triangularIsingCornerFactorConst e1 e2 t2 t3 ≠ 0 ∨ triangularIsingCornerFactorCoeff e1 e2 t2 t3 ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularIsingCornerFactor_const_coeff_not_both_zero e1 e2 t2 t3

/--
[triangularIsingCornerFactor_ne_zero_of_ne_forbidden](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingCornerFactor_ne_zero_of_ne_forbidden_eq
  {e1 e2 : Fin 2}
  {t1 t2 t3 : Real}
-- given
  (hne : t1 ≠ triangularIsingCornerForbiddenRoot e1 e2 t2 t3) :
-- imply
  triangularIsingCornerFactor e1 e2 t1 t2 t3 ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularIsingCornerFactor_ne_zero_of_ne_forbidden e1 e2 t1 t2 t3 hne

/--
[triangularIsingInner_discriminant_eq_zero_imp_cos_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingInner_discriminant_eq_zero_imp_cos_sq_eq
  {J1 J2 J3 k1 : Real}
-- given
  (hzero : triangularIsingInnerA J1 J2 J3 k1 ^ 2 - (triangularIsingInnerU J2 J3 k1 ^ 2 + triangularIsingInnerV J3 k1 ^ 2) = 0) :
-- imply
  Real.cos k1 ^ 2 = 1 := by
-- proof
  apply StatMech.FrontierA.triangularIsingInner_discriminant_eq_zero_imp_cos_sq J1 J2 J3 k1 hzero

/--
[exists_triangularIsingCornerSign_of_cos_sq_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma exists_triangularIsingCornerSign_of_cos_sq_eq_one_eq
  {k : Real}
-- given
  (hcos : Real.cos k ^ 2 = 1) :
-- imply
  ∃ e : Fin 2, Real.cos k = triangularIsingZ2Sign e ∧ Real.sin k = 0 := by
-- proof
  apply StatMech.FrontierA.exists_triangularIsingCornerSign_of_cos_sq_eq_one hcos

/--
[triangularIsingSymbol_zero_imp_discriminant_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingSymbol_zero_imp_discriminant_zero_eq
  {J1 J2 J3 k1 k2 : Real}
-- given
  (hzero : triangularIsingSymbol J1 J2 J3 k1 k2 = 0) :
-- imply
  triangularIsingInnerA J1 J2 J3 k1 ^ 2 - (triangularIsingInnerU J2 J3 k1 ^ 2 + triangularIsingInnerV J3 k1 ^ 2) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_zero_imp_discriminant_zero J1 J2 J3 k1 k2 hzero

/--
[cos_triangularIsingCornerMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma cos_triangularIsingCornerMomentum_eq
  {e : Fin 2} :
-- imply
  Real.cos (triangularIsingCornerMomentum e) = triangularIsingZ2Sign e := by
-- proof
  apply StatMech.FrontierA.cos_triangularIsingCornerMomentum e

/--
[sin_triangularIsingCornerMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma sin_triangularIsingCornerMomentum_eq
  {e : Fin 2} :
-- imply
  Real.sin (triangularIsingCornerMomentum e) = 0 := by
-- proof
  apply StatMech.FrontierA.sin_triangularIsingCornerMomentum e

/--
[exists_triangularIsingSymbol_corner_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma exists_triangularIsingSymbol_corner_zero_eq
  {J1 J2 J3 k1 k2 : Real}
-- given
  (hzero : triangularIsingSymbol J1 J2 J3 k1 k2 = 0) :
-- imply
  ∃ e1 e2 : Fin 2, triangularIsingSymbol J1 J2 J3 (triangularIsingCornerMomentum e1) (triangularIsingCornerMomentum e2) = 0 := by
-- proof
  apply StatMech.FrontierA.exists_triangularIsingSymbol_corner_zero J1 J2 J3 k1 k2 hzero

/--
[triangularIsingSymbol_pos_of_cornerFactors_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma triangularIsingSymbol_pos_of_cornerFactors_ne_zero_eq
  {J1 J2 J3 : Real}
-- given
  (hcorner : ∀ e1 e2 : Fin 2, triangularIsingCornerFactor e1 e2 (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) ≠ 0) :
-- imply
  ∀ k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2 := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_pos_of_cornerFactors_ne_zero J1 J2 J3 hcorner

/--
[exists_tanh_perturb_avoiding_triangularIsingCorners](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma exists_tanh_perturb_avoiding_triangularIsingCorners_eq
  {t1 t2 t3 epsilon : Real}
-- given
  (ht1lo : -1 < t1)
  (ht1hi : t1 < 1)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ t : Real, -1 < t ∧ t < 1 ∧ := by
-- proof
  apply StatMech.FrontierA.exists_tanh_perturb_avoiding_triangularIsingCorners t1 t2 t3 epsilon ht1lo ht1hi hepsilon

/--
[continuousAt_artanh_of_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma continuousAt_artanh_of_mem_Ioo_eq
  {t : Real}
-- given
  (htlo : -1 < t)
  (hthi : t < 1) :
-- imply
  ContinuousAt Real.artanh t := by
-- proof
  apply StatMech.FrontierA.continuousAt_artanh_of_mem_Ioo htlo hthi

/--
[exists_triangularIsingSymbol_pos_approx_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean)
-/
@[path]
private lemma exists_triangularIsingSymbol_pos_approx_first_eq
  {J1 J2 J3 epsilon : Real}
-- given
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ K1 : Real, := by
-- proof
  apply StatMech.FrontierA.exists_triangularIsingSymbol_pos_approx_first J1 J2 J3 epsilon hepsilon


-- created on 2026-10-23
