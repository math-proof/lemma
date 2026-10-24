import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Lem2226
open RayClassField GlobalConductor
open scoped NumberField


namespace GlobalConductor

/--
[localConductorAtFinitePlace_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2226.lean)
-/
@[path]
lemma localConductorAtFinitePlace_mono
  {K : Type u}
  {L₁ : Type u}
  {L₂ : Type u}
  [Field K]
  [NumberField K]
  [Field L₁]
  [NumberField L₁]
  [Algebra K L₁]
  [FiniteDimensional K L₁]
  [IsGalois K L₁]
  [Field L₂]
  [NumberField L₂]
  [Algebra K L₂]
  [FiniteDimensional K L₂]
  [IsGalois K L₂]
  {f : L₁ →ₐ[K] L₂}
  {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} :
-- imply
  localConductorAtFinitePlace K L₁ 𝔭 ≤ localConductorAtFinitePlace K L₂ 𝔭 := by
-- proof
  classical
  unfold localConductorAtFinitePlace
  exact Nat.find_mono (fun n => FinitePlaceHigherUnitsInNormGroup_of_sub K L₁ L₂ f 𝔭 n)

end GlobalConductor

namespace GlobalConductor

/--
[localConductorAtInfinitePlace_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2226.lean)
-/
@[path]
lemma localConductorAtInfinitePlace_mono
  {K : Type u}
  {L₁ : Type u}
  {L₂ : Type u}
  [Field K]
  [NumberField K]
  [Field L₁]
  [NumberField L₁]
  [Algebra K L₁]
  [FiniteDimensional K L₁]
  [IsGalois K L₁]
  [Field L₂]
  [NumberField L₂]
  [Algebra K L₂]
  [FiniteDimensional K L₂]
  [IsGalois K L₂]
  {f : L₁ →ₐ[K] L₂}
  {v : NumberField.InfinitePlace K} :
-- imply
  localConductorAtInfinitePlace K L₁ v ≤ localConductorAtInfinitePlace K L₂ v := by
-- proof
  classical
  unfold localConductorAtInfinitePlace
  by_cases h₁ : NumberField.InfinitePlace.IsUnramifiedIn L₁ v
  · simp [h₁]
  · simp only [if_neg h₁]
    suffices ¬NumberField.InfinitePlace.IsUnramifiedIn L₂ v by simp [this]
    rw [NumberField.InfinitePlace.IsUnramifiedIn] at h₁ ⊢
    push_neg at h₁ ⊢
    obtain ⟨w₁, hw₁, hram₁⟩ := h₁
    letI : Algebra L₁ L₂ := f.toRingHom.toAlgebra
    haveI : IsScalarTower K L₁ L₂ := by
      constructor
      intro x y z
      simp only [Algebra.smul_def]
      show f (algebraMap K L₁ x * y) * z = algebraMap K L₂ x * (f y * z)
      rw [map_mul, f.commutes]; ring
    haveI : FiniteDimensional L₁ L₂ := Module.Finite.of_restrictScalars_finite K L₁ L₂
    haveI : Algebra.IsAlgebraic L₁ L₂ := Algebra.IsAlgebraic.of_finite L₁ L₂
    obtain ⟨w₂, hw₂⟩ := NumberField.InfinitePlace.comap_surjective (k := L₁) (K := L₂) w₁
    have key : w₂.comap (f : L₁ →+* L₂) = w₁ := hw₂
    refine ⟨w₂, ?_, ?_⟩
    ·
      show w₂.comap (algebraMap K L₂) = v
      have : w₂.comap (algebraMap K L₂) =
        w₂.comap ((f : L₁ →+* L₂).comp (algebraMap K L₁)) := by
        congr 1; exact f.comp_algebraMap.symm
      rw [this]
      show (w₂.comap (f : L₁ →+* L₂)).comap (algebraMap K L₁) = v
      rw [key, hw₁]
    ·
      intro hram₂
      apply hram₁
      rw [← key]
      exact hram₂.comap_algHom f

end GlobalConductor

namespace GlobalConductor

/--
[conductorModulus_dvd_of_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2226.lean)
-/
@[path]
lemma conductorModulus_dvd_of_sub
  {K : Type u}
  {L₁ : Type u}
  {L₂ : Type u}
  [Field K]
  [NumberField K]
  [Field L₁]
  [NumberField L₁]
  [Algebra K L₁]
  [FiniteDimensional K L₁]
  [IsGalois K L₁]
  [Field L₂]
  [NumberField L₂]
  [Algebra K L₂]
  [FiniteDimensional K L₂]
  [IsGalois K L₂]
  {f : L₁ →ₐ[K] L₂} :
-- imply
  Modulus.dvd (conductorModulus K L₁) (conductorModulus K L₂) := by
-- proof
  intro v
  match v with
  | Place.finite 𝔭 =>
    exact localConductorAtFinitePlace_mono K L₁ L₂ f 𝔭
  | Place.infinite w =>
    exact localConductorAtInfinitePlace_mono K L₁ L₂ f w

end GlobalConductor

namespace GlobalConductor

/--
[lemma_22_26](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2226.lean)
-/
@[path]
lemma lemma_22_26
  {K : Type u}
  {L₁ : Type u}
  {L₂ : Type u}
  [Field K]
  [NumberField K]
  [Field L₁]
  [NumberField L₁]
  [Algebra K L₁]
  [FiniteDimensional K L₁]
  [IsGalois K L₁]
  [Field L₂]
  [NumberField L₂]
  [Algebra K L₂]
  [FiniteDimensional K L₂]
  [IsGalois K L₂]
  {f : L₁ →ₐ[K] L₂} :
-- imply
  Modulus.dvd (GlobalCFT.extensionConductor K L₁) (GlobalCFT.extensionConductor K L₂) := by
-- proof
  rw [← conductorModulus_eq_extensionConductor K L₁,
    ← conductorModulus_eq_extensionConductor K L₂]
  exact conductorModulus_dvd_of_sub K L₁ L₂ f
end GlobalConductor
namespace LocalConductor
end LocalConductor



-- created on 2026-10-23
