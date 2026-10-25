import Mathlib
import sympy.Basic
import Lemma.ModularCurve.LaurentCoeff
import Lemma.ModularCurve.QExpansionDiff
open ModularCurve


private lemma coeffMap_single_one
  {R K : Type*}
  [CommRing R]
  [Field K]
  (φ : R →+* K) :
  coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R)) = HahnSeries.single (1 : ℤ) (1 : K) := by
  ext n
  rw [coeffMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

private lemma derivative_coeffMap
  {R K : Type*}
  [CommRing R]
  [Field K]
  (φ : R →+* K) (w : LaurentSeries R) :
  LaurentSeries.derivative K (coeffMap φ w) = coeffMap φ (LaurentSeries.derivative R w) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, coeffMap_coeff,
    coeffMap_coeff, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, map_zsmul]

private lemma thetaL_coeffMap_impl
  {R K : Type*}
  [CommRing R]
  [Field K]
  (φ : R →+* K) (w : LaurentSeries R) :
  thetaL K (coeffMap φ w) =
    coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) := by
  rw [thetaL_apply, derivative_coeffMap, map_mul, coeffMap_single_one]
/--
[ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean)
-/
@[path]
private lemma main
  [CommRing R] [Field K]
  {φ : R →+* K}
  {w : LaurentSeries R} :
-- imply
  ModularCurve.thetaL K (ModularCurve.coeffMap φ w) =
      ModularCurve.coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) :=
-- proof
  thetaL_coeffMap_impl φ w


-- created on 2026-10-23
