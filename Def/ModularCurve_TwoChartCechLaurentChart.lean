module

public import Mathlib
public import Def.AlgebraicGeometry_TwoChartCech
public import Structure.AlgebraicGeometry_TwoChartCechLaurentChart
public import Abbrev.AlgebraicGeometry_TwoChartCechLaurentChart

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace LaurentSeries

variable (R : Type*) [CommRing R]

def residue : LaurentSeries R →ₗ[R] R := HahnSeries.coeff.linearMap (-1)

end LaurentSeries

namespace TwoChartCech.Cover

variable {R : Type u} [CommRing R]


namespace LaurentChart

variable {𝒰 : Cover.{u, v} R} (Λ : 𝒰.LaurentChart)

def expandLinear : 𝒰.A01 →ₗ[R] LaurentSeries R where
  toFun := Λ.expand
  map_add' := map_add _
  map_smul' := Λ.expand_smul

def expandDerivation :
    letI := Λ.expandModule
    Derivation R 𝒰.A01 (LaurentSeries R) :=
  letI := Λ.expandModule
  Derivation.mk' (LaurentSeries.derivative R ∘ₗ Λ.expandLinear) fun f g => by
    change LaurentSeries.derivative R (Λ.expand (f * g)) =
      Λ.expand f * LaurentSeries.derivative R (Λ.expand g) + Λ.expand g * LaurentSeries.derivative R (Λ.expand f)
    rw [map_mul, LaurentSeries.derivative_mul_def, mul_comm (LaurentSeries.derivative R (Λ.expand f))]

def expandKaehler :
    letI := Λ.expandModule
    Ω[𝒰.A01⁄R] →ₗ[𝒰.A01] LaurentSeries R :=
  letI := Λ.expandModule
  haveI := Λ.isScalarTower_expandModule
  Λ.expandDerivation.liftKaehlerDifferential

def residue : Ω[𝒰.A01⁄R] →ₗ[R] R where
  toFun ω := letI := Λ.expandModule; LaurentSeries.residue R (Λ.expandKaehler ω)
  map_add' ω ω' := by
    letI := Λ.expandModule
    change LaurentSeries.residue R (Λ.expandKaehler (ω + ω')) = _
    rw [map_add, map_add]
  map_smul' r ω := by
    letI := Λ.expandModule
    haveI := Λ.isScalarTower_expandModule
    change LaurentSeries.residue R (Λ.expandKaehler (r • ω)) = r • LaurentSeries.residue R (Λ.expandKaehler ω)
    have h1 : Λ.expandKaehler (r • ω) = r • Λ.expandKaehler ω := by
      rw [← IsScalarTower.algebraMap_smul 𝒰.A01 r ω, LinearMap.map_smul]
      change Λ.expand (algebraMap R 𝒰.A01 r) * Λ.expandKaehler ω = _
      rw [expand_algebraMap, HahnSeries.C_mul_eq_smul]
    rw [h1, map_smul]

def HasParameter {B : Type*} [CommRing B] [Algebra R B] (ρ : B →ₐ[R] 𝒰.A01) : Prop :=
  ∃ b : B, Λ.expand (ρ b) = HahnSeries.single 1 1

end LaurentChart

def formalDisc (R : Type u) [CommRing R] : Cover.{u, u} R :=
  letI : Algebra R (LaurentSeries R) := (HahnSeries.C : R →+* LaurentSeries R).toAlgebra
  letI : Algebra R (PowerSeries R) := inferInstance
  { A0 := LaurentSeries R
    A1 := PowerSeries R
    A01 := LaurentSeries R
    ρ0 := AlgHom.id R _
    ρ1 := { (HahnSeries.ofPowerSeries ℤ R) with
      commutes' := fun r => by
        change HahnSeries.ofPowerSeries ℤ R (algebraMap R (PowerSeries R) r) = HahnSeries.C r
        rw [PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C] } }

def formalDiscChart (R : Type u) [CommRing R] : (formalDisc R).LaurentChart where
  expand := RingHom.id _
  expand_algebraMap _ := rfl

end TwoChartCech.Cover


namespace TwoChartCech.Cover

def formalDiscPoint (R : Type u) [CommRing R] : (formalDisc R).A1 →ₐ[R] R :=
  { (PowerSeries.constantCoeff : PowerSeries R →+* R) with
    commutes' := fun r => by
      change PowerSeries.constantCoeff (algebraMap R (PowerSeries R) r) = r
      rw [PowerSeries.algebraMap_eq]
      exact PowerSeries.constantCoeff_C r }

end TwoChartCech.Cover

end

end
