module

public import Mathlib
public import Theorem.Polynomial.WeierstrassLevelCarrier
public import Def.ModularCurve_WeierstrassLevelModuliDatum
public import Def.ModularCurve_WeierstrassLevelComponents
public import Theorem.WeierstrassCurve.WeierstrassGamma0Sqf
public import Def.WeierstrassCurve_DrinfeldBasisGlobal
public import Def.WeierstrassCurve_DrinfeldTransportPin
public import Def.WeierstrassCurve_SectionAtOrigin
public import Def.WeierstrassCurve_DrinfeldLevelFunctor
public import Structure.ModularCurve_WeierstrassGamma0Pow

public noncomputable section

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)


public theorem IsCyclicGenKernel.monic {p k : ℕ} {h : T[X]} (hh : W.IsCyclicGenKernel p k h) : h.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hh.natDegree_le hh.coeff_eq_one


public theorem IsCyclicGenKernel.map {T' : Type u} [CommRing T'] (f : T →+* T') {p k : ℕ} {h : T[X]}
    (hh : W.IsCyclicGenKernel p k h) : (W.map f).IsCyclicGenKernel p k (h.map f) where
  natDegree_le := (Polynomial.natDegree_map_le).trans hh.natDegree_le
  coeff_eq_one := by rw [Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  mul_preΨ_dvd := by
    rw [WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ, ← Polynomial.map_mul]
    exact Polynomial.map_dvd f hh.mul_preΨ_dvd
  dvd_smulNumerator := fun a ha ha' hpa => by
    rw [W.smulNumerator_map f]; exact Polynomial.map_dvd f (hh.dvd_smulNumerator a ha ha' hpa)

end WeierstrassCurve

namespace ModularCurve

variable {T : Type u} [CommRing T]


public theorem isGamma0PowAt_of_pow_eq_two (W : WeierstrassCurve T) {p k : ℕ} (hpk : p ^ k = 2) (h : T[X]) :
    IsGamma0PowAt W p k h ↔ W.IsTwoKernel h := by
  simp [IsGamma0PowAt, hpk]


public theorem isGamma0PowAt_of_pow_ne_two (W : WeierstrassCurve T) {p k : ℕ} (hpk : p ^ k ≠ 2) (h : T[X]) :
    IsGamma0PowAt W p k h ↔ W.IsCyclicGenKernel p k h := by
  simp [IsGamma0PowAt, hpk]


public theorem IsGamma0PowAt.map {T' : Type u} [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T) (p k : ℕ) {h : T[X]}
    (hh : IsGamma0PowAt W p k h) : IsGamma0PowAt (W.map f) p k (h.map f) := by
  by_cases hpk : p ^ k = 2
  · exact (isGamma0PowAt_of_pow_eq_two _ hpk _).2 (((isGamma0PowAt_of_pow_eq_two _ hpk _).1 hh).map W f)
  · exact (isGamma0PowAt_of_pow_ne_two _ hpk _).2 (((isGamma0PowAt_of_pow_ne_two _ hpk _).1 hh).map W f)

