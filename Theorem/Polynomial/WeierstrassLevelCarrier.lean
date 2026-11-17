module

public import Mathlib
public import Def.ModularCurve_WeierstrassLevelCarrier
public import Structure.ModularCurve_WeierstrassLevelCarrier

public noncomputable section

set_option autoImplicit false

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type*} [CommRing T] (W : WeierstrassCurve T)


public theorem IsCyclicKernel.monic {N : ℕ} {h : T[X]} (hh : W.IsCyclicKernel N h) : h.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hh.natDegree_le hh.coeff_eq_one

section Map

variable {T' : Type*} [CommRing T'] (f : T →+* T')

public theorem smulNumerator_map (a d : ℕ) (h : T[X]) :
    (W.map f).smulNumerator a d (h.map f) = (W.smulNumerator a d h).map f := by
  simp only [smulNumerator, Polynomial.coeff_map, WeierstrassCurve.map_Φ,
    WeierstrassCurve.map_ΨSq, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C]

public theorem IsCyclicKernel.map {N : ℕ} {h : T[X]} (hh : W.IsCyclicKernel N h) :
    (W.map f).IsCyclicKernel N (h.map f) where
  natDegree_le := (Polynomial.natDegree_map_le).trans hh.natDegree_le
  coeff_eq_one := by rw [Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  dvd_preΨ := by rw [WeierstrassCurve.map_preΨ]; exact Polynomial.map_dvd f hh.dvd_preΨ
  dvd_smulNumerator := fun a ha ha' => by
    rw [W.smulNumerator_map f]; exact Polynomial.map_dvd f (hh.dvd_smulNumerator a ha ha')

end Map


public theorem jOfUnit_eq_j [W.IsElliptic] (hΔ : IsUnit W.Δ) : W.jOfUnit hΔ = W.j := rfl

public theorem jOfUnit_map {T' : Type*} [CommRing T'] (f : T →+* T') (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (W.map f).Δ) :
    (W.map f).jOfUnit hΔ' = f (W.jOfUnit hΔ) := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  exact W.map_j f

public theorem jOfUnit_variableChange (C : VariableChange T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (C • W).Δ) :
    (C • W).jOfUnit hΔ' = W.jOfUnit hΔ := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  exact W.variableChange_j C

public theorem isUnit_Δ_map {T' : Type*} [CommRing T'] (f : T →+* T') (hΔ : IsUnit W.Δ) : IsUnit (W.map f).Δ := by
  rw [W.map_Δ]; exact hΔ.map f

public theorem isUnit_Δ_variableChange (C : VariableChange T) (hΔ : IsUnit W.Δ) : IsUnit (C • W).Δ := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  exact (C • W).isUnit_Δ

end WeierstrassCurve

end
