import Mathlib
import Structure.AlgebraicGeometry_TwoChartCech

set_option autoImplicit false

noncomputable section

universe u v

namespace LaurentSeries

variable (R : Type*) [CommRing R]


end LaurentSeries

namespace TwoChartCech.Cover

variable {R : Type u} [CommRing R]

structure LaurentChart (𝒰 : Cover.{u, v} R) where

  expand : 𝒰.A01 →+* LaurentSeries R

  expand_algebraMap : ∀ r : R, expand (algebraMap R 𝒰.A01 r) = HahnSeries.C r

namespace LaurentChart

variable {𝒰 : Cover.{u, v} R} (Λ : 𝒰.LaurentChart)


def IsRegular {B : Type*} [CommRing B] [Algebra R B] (ρ : B →ₐ[R] 𝒰.A01) : Prop :=
  ∀ b : B, Λ.expand (ρ b) ∈ (HahnSeries.ofPowerSeries ℤ R).range


end LaurentChart


end TwoChartCech.Cover

namespace TwoChartCech.Cover.LaurentChart

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R}

structure IsCompletionAlong (Λ : 𝒰.LaurentChart) {B : Type*} [CommRing B] [Algebra R B]
    (ρ : B →ₐ[R] 𝒰.A01) (e : B →ₐ[R] R) : Prop where

  isRegular : Λ.IsRegular ρ

  exists_coeff_eq : ∀ (n : ℕ) (p : PowerSeries R), ∃ b : B,
    ∀ k : ℕ, k < n → (Λ.expand (ρ b)).coeff (k : ℤ) = PowerSeries.coeff k p

  forall_coeff_eq_zero_iff : ∀ (n : ℕ) (b : B),
    (∀ k : ℕ, k < n → (Λ.expand (ρ b)).coeff (k : ℤ) = 0) ↔ b ∈ RingHom.ker e.toRingHom ^ n

end TwoChartCech.Cover.LaurentChart


namespace TwoChartCech.Cover


end TwoChartCech.Cover

end
