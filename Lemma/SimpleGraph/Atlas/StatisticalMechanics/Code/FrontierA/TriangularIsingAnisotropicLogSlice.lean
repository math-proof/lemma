import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingAnisotropicLogSlice
open MeasureTheory StatMech StatMech.FrontierA


/--
[one_add_abs_sinh_mul_le_cosh_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingAnisotropicLogSlice.lean)
-/
@[path]
private lemma one_add_abs_sinh_mul_le_cosh_mul_eq
  {x y : Real} :
-- imply
  1 + |Real.sinh x * Real.sinh y| <= Real.cosh x * Real.cosh y := by
-- proof
  apply StatMech.FrontierA.one_add_abs_sinh_mul_le_cosh_mul x y

/--
[abs_sinh_lt_cosh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingAnisotropicLogSlice.lean)
-/
@[path]
private lemma abs_sinh_lt_cosh_eq
  {x : Real} :
-- imply
  |Real.sinh x| < Real.cosh x := by
-- proof
  apply StatMech.FrontierA.abs_sinh_lt_cosh x

/--
[triangularIsingSliceA_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingAnisotropicLogSlice.lean)
-/
@[path]
private lemma triangularIsingSliceA_pos_eq
  {J1 J2 J3 p : Real} :
-- imply
  0 < triangularIsingSliceA J1 J2 J3 p := by
-- proof
  apply StatMech.FrontierA.triangularIsingSliceA_pos J1 J2 J3 p

/--
[triangularIsingSymbol_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingAnisotropicLogSlice.lean)
-/
@[path]
private lemma triangularIsingSymbol_eq_slice_eq
  {J1 J2 J3 p q : Real} :
-- imply
  triangularIsingSymbol J1 J2 J3 p q = triangularIsingSliceA J1 J2 J3 p - triangularIsingSliceU J2 J3 p * Real.cos q - triangularIsingSliceV J3 p * Real.sin q := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_eq_slice J1 J2 J3 p q

/--
[triangularIsingSlice_discriminant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingAnisotropicLogSlice.lean)
-/
@[path]
private lemma triangularIsingSlice_discriminant_nonneg_eq
  {J1 J2 J3 p : Real}
-- given
  (hA : 0 < triangularIsingSliceA J1 J2 J3 p)
  (hnonneg : forall q, 0 <= triangularIsingSymbol J1 J2 J3 p q) :
-- imply
  0 <= triangularIsingSliceA J1 J2 J3 p ^ 2 - (triangularIsingSliceU J2 J3 p ^ 2 + triangularIsingSliceV J3 p ^ 2) := by
-- proof
  apply StatMech.FrontierA.triangularIsingSlice_discriminant_nonneg hA hnonneg

/--
[integral_log_triangularIsingSymbol_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingAnisotropicLogSlice.lean)
-/
@[path]
private lemma integral_log_triangularIsingSymbol_slice_eq
  {J1 J2 J3 p : Real}
-- given
  (hA : 0 < triangularIsingSliceA J1 J2 J3 p)
  (hnonneg : forall q, 0 <= triangularIsingSymbol J1 J2 J3 p q) :
-- imply
  (∫ q in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 p q)) = 2 * Real.pi * Real.log (nonnegativeSinusoidQ (triangularIsingSliceA J1 J2 J3 p) (triangularIsingSliceU J2 J3 p) (triangularIsingSliceV J3 p) / 2) := by
-- proof
  apply StatMech.FrontierA.integral_log_triangularIsingSymbol_slice hA hnonneg


-- created on 2026-10-23
