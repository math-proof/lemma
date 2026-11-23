module

public import Mathlib
public import Theorem.Polynomial.WeierstrassLevelCarrier
public import Def.ModularCurve_WeierstrassLevelModuliDatum
public import Def.ModularCurve_WeierstrassLevelComponents
public import Def.WeierstrassCurve_DrinfeldBasisGlobal
public import Def.WeierstrassCurve_DrinfeldTransportPin
public import Def.WeierstrassCurve_SectionAtOrigin
public import Def.WeierstrassCurve_DrinfeldLevelFunctor
public import Structure.ModularCurve_WeierstrassGamma0Sqf

public noncomputable section

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)


public theorem IsTwoKernel.monic {h : T[X]} (hh : W.IsTwoKernel h) : h.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hh.natDegree_le hh.coeff_eq_one


public theorem IsTwoKernel.map {T' : Type u} [CommRing T'] (f : T →+* T') {h : T[X]} (hh : W.IsTwoKernel h) :
    (W.map f).IsTwoKernel (h.map f) where
  natDegree_le := (Polynomial.natDegree_map_le).trans hh.natDegree_le
  coeff_eq_one := by rw [Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  dvd_Ψ₂Sq := by rw [WeierstrassCurve.map_Ψ₂Sq]; exact Polynomial.map_dvd f hh.dvd_Ψ₂Sq

end WeierstrassCurve

namespace ModularCurve

variable {T : Type u} [CommRing T]


public theorem isGamma0At_two (W : WeierstrassCurve T) (h : T[X]) : IsGamma0At W 2 h ↔ W.IsTwoKernel h := by
  simp [IsGamma0At]


public theorem isGamma0At_of_ne_two (W : WeierstrassCurve T) {p : ℕ} (hp : p ≠ 2) (h : T[X]) :
    IsGamma0At W p h ↔ W.IsCyclicKernel p h := by
  simp [IsGamma0At, hp]


public theorem IsGamma0At.map {T' : Type u} [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T) (p : ℕ) {h : T[X]}
    (hh : IsGamma0At W p h) : IsGamma0At (W.map f) p (h.map f) := by
  by_cases hp : p = 2
  · subst hp
    exact (isGamma0At_two _ _).2 (((isGamma0At_two _ _).1 hh).map W f)
  · exact (isGamma0At_of_ne_two _ hp _).2 (((isGamma0At_of_ne_two _ hp _).1 hh).map W f)

