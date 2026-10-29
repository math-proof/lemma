import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


namespace MetaMathlibExt

/--
[spectralNorm_le_one_iff_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SpectralNormUnitBall.lean)
-/
@[path]
lemma spectralNorm_le_one_iff_isIntegral
  [CommRing A] [IsDomain A] [NontriviallyNormedField K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]   [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L]
-- given
  (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y)
  (x : L) :
-- imply
  spectralNorm K L x ≤ 1 ↔ IsIntegral A x := by
-- proof
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
      rwa [eval_map]
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
      rwa [Polynomial.aeval_map_algebraMap]
    have hdvd : minpoly K x ∣ p.map (algebraMap A K) :=
      minpoly.dvd K x hqroot
    have hcoeffInt : ∀ n : ℕ, IsIntegral A ((minpoly K x).coeff n) :=
      fun n => Polynomial.isIntegral_coeff_of_dvd _ _ hpmonic hmonic hdvd n
    have hcoeff : ∀ n : ℕ, ‖(minpoly K x).coeff n‖ ≤ 1 :=
      fun n => (hA _).mpr (hcoeffInt n)
    have h := (spectralValue_le_one_iff hmonic).mpr hcoeff
    simpa [spectralNorm] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[spectralNorm_le_one_iff_exists_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SpectralNormUnitBall.lean)
-/
@[path]
lemma spectralNorm_le_one_iff_exists_integralClosure
  [CommRing A] [IsDomain A] [NontriviallyNormedField K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  {x : L}
-- given
  (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y) :
-- imply
  spectralNorm K L x ≤ 1 ↔ ∃ b : B, algebraMap B L b = x := by
-- proof
  rw [spectralNorm_le_one_iff_isIntegral hA x]
  exact IsIntegralClosure.isIntegral_iff

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
