import Mathlib
import Instance.ModularCurve_JHNeronObjectAtP
import Structure.AlgebraicCurve_RegularProlongation

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups
set_option quotPrecheck false

namespace ModularCurve

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
variable (A : ValuationSubring (AlgebraicClosure ℚ))

namespace JHPlaceSpecialization


end JHPlaceSpecialization

variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

local notation "κ" => ResidueField ↥A
local notation "FM" => ↥(xHFunctionFieldBar M H)
local notation "FMp" => ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
local notation "Γ′" => ModularCurve.JHNeronObjectAtP.ΓN p M H hpM

namespace JHPlaceSpecialization


end JHPlaceSpecialization

structure JHPlaceSpecialization where

  sp : Place (AlgebraicClosure ℚ) FMp → Place κ Fb

  spPic0 : Pic0 (AlgebraicClosure ℚ) FMp →+ Pic0 κ Fb

  d0_qexp : ∀ (f : FMp) (y : LaurentSeries ↥A),
    coeffMap A.subtype y = ((f : FMp) : LaurentSeries (AlgebraicClosure ℚ)) →
    ∀ g : Fb, ((g : Fb) : LaurentSeries κ) = coeffMap (IsLocalRing.residue ↥A) y → g ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) FMp, (∀ v, D v = v.ord f) →
      ∀ v' : Place κ Fb, Finsupp.mapDomain sp D v' = v'.ord g

  d4 : Function.Surjective sp

  d5 : ∀ f : FMp, f ≠ 0 → ∀ D : Divisor (AlgebraicClosure ℚ) FMp, (∀ v, D v = v.ord f) →
    ∃ g : Fb, g ≠ 0 ∧ ∀ v' : Place κ Fb, Finsupp.mapDomain sp D v' = v'.ord g

  d6_inertia : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
    ∀ w : Place (AlgebraicClosure ℚ) FMp,
      sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) = sp w

  d6_frobenius : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p →
    ∀ w : Place (AlgebraicClosure ℚ) FMp,
      sp (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM)) σ • w) =
        qExpFrobeniusPlaceModL κ Γ′ p (sp w)

  spPic0_compat : ∀ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := FMp),
    ∃ D' : Divisor.degZero (K := κ) (F := Fb),
      (D' : Divisor κ Fb) = Finsupp.mapDomain sp (D : Divisor (AlgebraicClosure ℚ) FMp) ∧ spPic0 (Pic0.mk D) = Pic0.mk D'

namespace JHPlaceSpecialization

variable {p M H hpM A}


open Classical in


open Classical in


structure ProlongationDatum (P : JHPlaceSpecialization p M H hpM A) (θ : FM ≃ₐ[AlgebraicClosure ℚ] FM) where

  R₁ : RegularProlongation A FM Fb

  R₂ : RegularProlongation A FM Fb

  residue₁_coeffMap : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
    ∃ h : (⟨coeffMap A.subtype y, hy⟩ : FM) ∈ R₁.integers,
      ((R₁.residue ⟨_, h⟩ : Fb) : LaurentSeries κ) = coeffMap (IsLocalRing.residue ↥A) y

  mem_integers₂_iff : ∀ f : FM, f ∈ R₂.integers ↔ θ f ∈ R₁.integers
  residue₂_eq : ∀ (f : FM) (h : f ∈ R₂.integers), R₂.residue ⟨f, h⟩ = R₁.residue ⟨θ f, (mem_integers₂_iff f).mp h⟩

namespace ProlongationDatum

variable {P : JHPlaceSpecialization p M H hpM A}
variable {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}


open Classical in


open Classical in


end ProlongationDatum
end JHPlaceSpecialization

end ModularCurve

end
