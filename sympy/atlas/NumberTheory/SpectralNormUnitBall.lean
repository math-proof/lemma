/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SpectralNormUnitBall.lean -/

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.Tower

/-! # Spectral norm unit ball

Sound corrected unit-ball prerequisite for ATLAS item `N205`
(NumberTheoryI Theorem 10.4).
The ATLAS Lean statement gives `K` an arbitrary norm, while its two admitted
helpers implicitly identify `A` with the base closed unit ball; this module
records the explicit base-unit-ball hypothesis under which the conclusion holds.

Source (immutable):
https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/CDVRExtensions.lean#L215-L397

## ATLAS source-to-API map

ATLAS's admitted `norm_algebraMap_dvr_le_one` and the
`monic_irreducible_coeff_norm_le_one_lifts_to_DVR`/Theorem 10.4 unit-ball step
map to `spectralNorm_le_one_iff_isIntegral` and its integral-closure corollary
`spectralNorm_le_one_iff_exists_integralClosure`. This API repairs the missing
base compatibility hypothesis via the explicit `hA` hypothesis.
-/

namespace MetaMathlibExt

open Polynomial

/-- Unit ball of the spectral norm: under the essential base-unit-ball hypothesis
`hA` (the closed unit ball of `K` is exactly the integral closure of `A` in `K`),
the closed unit ball of the spectral norm on `L` is exactly the integral closure
of `A` in `L`. -/
theorem spectralNorm_le_one_iff_isIntegral
    {A K L : Type*} [CommRing A] [IsDomain A]
    [NontriviallyNormedField K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L]
    (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y) (x : L) :
    spectralNorm K L x ≤ 1 ↔ IsIntegral A x := by
  have hKalg : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hxInt : IsIntegral K x := (hKalg.isAlgebraic x).isIntegral
  have hmonic : (minpoly K x).Monic := minpoly.monic hxInt
  constructor
  · intro hle
    have hcoeff : ∀ n : ℕ, ‖(minpoly K x).coeff n‖ ≤ 1 :=
      (spectralValue_le_one_iff hmonic).mp (by simpa [spectralNorm] using hle)
    have hcoeffInt : ∀ n : ℕ, IsIntegral A ((minpoly K x).coeff n) :=
      fun n => (hA _).mp (hcoeff n)
    have hcoeffIntL : ∀ n : ℕ,
        IsIntegral A (algebraMap K L ((minpoly K x).coeff n)) := by
      intro n
      have h := (hcoeffInt n).map (IsScalarTower.toAlgHom A K L)
      simpa using h
    have hPmonic : ((minpoly K x).map (algebraMap K L)).Monic := hmonic.map _
    have hPdeg : ((minpoly K x).map (algebraMap K L)).natDegree ≠ 0 := by
      rw [hmonic.natDegree_map _]
      exact (minpoly.natDegree_pos hxInt).ne'
    have hPeval : Polynomial.eval x ((minpoly K x).map (algebraMap K L)) = 0 := by
      have h : aeval x (minpoly K x) = 0 := minpoly.aeval K x
      rw [aeval_def] at h
      rw [eval_map]
      exact h
    have hcoeffP : ∀ i, IsIntegral A (((minpoly K x).map (algebraMap K L)).coeff i) := by
      intro i
      rw [coeff_map]
      exact hcoeffIntL i
    have h0 : IsIntegral A (Polynomial.eval x ((minpoly K x).map (algebraMap K L))) := by
      rw [hPeval]; exact isIntegral_zero
    exact IsIntegral.of_aeval_monic_of_isIntegral_coeff hPmonic hPdeg h0 hcoeffP
  · intro hxA
    obtain ⟨p, hpmonic, hroot⟩ := hxA
    have hqroot : aeval x (p.map (algebraMap A K)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]
      exact hroot
    have hdvd : minpoly K x ∣ p.map (algebraMap A K) :=
      minpoly.dvd K x hqroot
    have hcoeffInt : ∀ n : ℕ, IsIntegral A ((minpoly K x).coeff n) :=
      fun n => Polynomial.isIntegral_coeff_of_dvd _ _ hpmonic hmonic hdvd n
    have hcoeff : ∀ n : ℕ, ‖(minpoly K x).coeff n‖ ≤ 1 :=
      fun n => (hA _).mpr (hcoeffInt n)
    have h := (spectralValue_le_one_iff hmonic).mpr hcoeff
    simpa [spectralNorm] using h

/-- Integral-closure corollary: under the same essential base-unit-ball hypothesis,
the spectral-norm unit ball is the image of any integral closure `B` of `A` in `L`. -/
theorem spectralNorm_le_one_iff_exists_integralClosure
    {A K L B : Type*} [CommRing A] [IsDomain A]
    [NontriviallyNormedField K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y) (x : L) :
    spectralNorm K L x ≤ 1 ↔ ∃ b : B, algebraMap B L b = x := by
  rw [spectralNorm_le_one_iff_isIntegral hA x]
  exact IsIntegralClosure.isIntegral_iff

end MetaMathlibExt
