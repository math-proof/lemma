/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Valuation.LocalSubring
import Def.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich
/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

lemma nos_coefficients_mem {R k K : Type*} [CommRing R] [Field k] [Field K]
    [Algebra R k] [Algebra k K] (E : WeierstrassCurve k) [E.IsIntegral R]
    (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range) :
    algebraMap k K E.a₁ ∈ A ∧ algebraMap k K E.a₂ ∈ A ∧
      algebraMap k K E.a₃ ∈ A ∧ algebraMap k K E.a₄ ∈ A ∧
      algebraMap k K E.a₆ ∈ A ∧ algebraMap k K E.Δ ∈ A := by
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₁, E.integralModel_a₁_eq R⟩
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₂, E.integralModel_a₂_eq R⟩
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₃, E.integralModel_a₃_eq R⟩
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₄, E.integralModel_a₄_eq R⟩
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₆, E.integralModel_a₆_eq R⟩
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).Δ, E.integralModel_Δ_eq R⟩

lemma nos_discriminant_unit {R k K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field k] [Algebra R k] [IsFractionRing R k]
    [Field K] [Algebra k K] (E : WeierstrassCurve k) [E.HasGoodReduction R]
    (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range) :
    ∃ d : A, (d : K) = algebraMap k K E.Δ ∧ IsUnit d := by
  let r : R := (E.integralModel R).Δ
  have hrval :
      IsDedekindDomain.HeightOneSpectrum.valuation
        k (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R k r) = 1 := by
    rw [show algebraMap R k r = E.Δ from E.integralModel_Δ_eq R]
    exact WeierstrassCurve.HasGoodReduction.goodReduction
  have hrnot : r ∉ (IsDiscreteValuationRing.maximalIdeal R).asIdeal :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := k)
      (IsDiscreteValuationRing.maximalIdeal R)).mp hrval
  have hr : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp (by
    simpa [IsDiscreteValuationRing.maximalIdeal] using hrnot)
  let f := nosToValuationSubring A hA
  refine ⟨f r, ?_, hr.map f⟩
  change algebraMap k K (algebraMap R k r) = algebraMap k K E.Δ
  rw [show algebraMap R k r = E.Δ from E.integralModel_Δ_eq R]

lemma nos_nat_unit {R k K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field k] [Algebra R k] [IsFractionRing R k]
    [Field K] [Algebra k K] (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]
    (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range) :
    ∃ u : A, (u : K) = (n : K) ∧ IsUnit u := by
  have hnres : IsLocalRing.residue R (n : R) ≠ 0 := by
    simpa using (NeZero.ne (n : IsLocalRing.ResidueField R))
  have hnnot : (n : R) ∉ IsLocalRing.maximalIdeal R := fun hn ↦
    hnres ((IsLocalRing.residue_eq_zero_iff (n : R)).mpr hn)
  have hn : IsUnit (n : R) := IsLocalRing.notMem_maximalIdeal.mp hnnot
  let f := nosToValuationSubring A hA
  refine ⟨f (n : R), ?_, hn.map f⟩
  change algebraMap k K (algebraMap R k (n : R)) = (n : K)
  simp

end MetaMathlibExt
