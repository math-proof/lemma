import Mathlib
import sympy.Basic
open Polynomial WeierstrassCurve


private lemma isLocalHom_powerSeriesC (R : Type*) [CommRing R] : IsLocalHom (PowerSeries.C (R := R)) := by
  refine ⟨fun a ha => ?_⟩
  rwa [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at ha

private lemma powerSeriesC_injective (R : Type*) [CommRing R] : Function.Injective (PowerSeries.C (R := R)) :=
  Function.LeftInverse.injective (g := PowerSeries.constantCoeff) fun a => PowerSeries.constantCoeff_C a

private lemma eval₂_C_X_powerSeries {R : Type*} [CommRing R] (P : Polynomial R) :
  P.eval₂ (PowerSeries.C (R := R)) PowerSeries.X = (P : PowerSeries R) := by
  have h : Polynomial.eval₂RingHom (PowerSeries.C (R := R)) PowerSeries.X =
      Polynomial.coeToPowerSeries.ringHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    ·
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact (Polynomial.coe_C a).symm
    ·
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      apply Polynomial.coe_X.symm
  refine congrArg (fun φ : Polynomial R →+* PowerSeries R => φ P) h

universe u

set_option maxHeartbeats 999999 in
set_option synthInstance.maxHeartbeats 999999 in
/--
[WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_valuationSubring_with_transcendental_of_charZero.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [CharZero k] :
-- imply
  ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L)
    (A : ValuationSubring L) (φ : k →+* L) (hφ : ∀ x, φ x ∈ A)
    (ι : k →+* IsLocalRing.ResidueField A),
    (∀ a : k, IsLocalRing.residue A ⟨φ a, hφ a⟩ = ι a) ∧
    ∃ (t : L) (ht : t ∈ A), (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
      ∀ P : Polynomial k, P ≠ 0 → P.eval₂ φ t ≠ 0 := by
-- proof
  classical
    have hR'0 : CharZero (PowerSeries k) :=
      charZero_of_injective_ringHom (f := PowerSeries.C (R := k)) (powerSeriesC_injective _)
    have : CharZero (FractionRing (PowerSeries k)) := IsFractionRing.charZero (PowerSeries k)
    have hL : CharZero (AlgebraicClosure (FractionRing (PowerSeries k))) :=
      charZero_of_injective_algebraMap (algebraMap (FractionRing (PowerSeries k)) _).injective
    let ψ : PowerSeries k →+* AlgebraicClosure (FractionRing (PowerSeries k)) :=
      (algebraMap (FractionRing (PowerSeries k)) _).comp (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))
    have hψ : Function.Injective ψ :=
      (algebraMap (FractionRing (PowerSeries k)) _).injective.comp (IsFractionRing.injective (PowerSeries k) _)
    obtain ⟨A, hAmem, hAloc⟩ := IsLocalRing.exists_factor_valuationRing ψ
    let g : PowerSeries k →+* A := ψ.codRestrict A.toSubring hAmem
    have : IsLocalHom g := hAloc
    let φ : k →+* AlgebraicClosure (FractionRing (PowerSeries k)) := ψ.comp (PowerSeries.C (R := k))
    have hφ : ∀ x, φ x ∈ A := fun x => hAmem _
    refine ⟨AlgebraicClosure (FractionRing (PowerSeries k)), inferInstance, inferInstance, hL,
      A, φ, hφ, (IsLocalRing.residue A).comp (g.comp (PowerSeries.C (R := k))), fun a => rfl,
      ψ PowerSeries.X, hAmem _, ?_, ?_⟩
    ·
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hX : IsUnit (PowerSeries.X : PowerSeries k) := IsUnit.of_map g _ hu
      rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X] at hX
      exact not_isUnit_zero hX
    ·
      intro P hP h0
      apply hP
      rw [show P.eval₂ φ (ψ PowerSeries.X) = ψ (P.eval₂ (PowerSeries.C (R := k)) PowerSeries.X)
        from (Polynomial.hom_eval₂ P _ ψ PowerSeries.X).symm, eval₂_C_X_powerSeries] at h0
      exact Polynomial.coe_eq_zero_iff.mp (hψ (by rw [h0, map_zero]))


-- created on 2026-10-23
