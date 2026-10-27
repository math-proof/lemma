import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Ch22Conductor
open RayClassField Classical in LocalConductor GlobalConductor
open scoped NumberField


namespace LocalConductor

/--
[HigherUnitsInNormGroup_of_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean)
-/
@[path]
lemma HigherUnitsInNormGroup_of_sub
  {K L₁ L₂ : Type*}
  [IsLocalField K]
  [IsLocalField L₁]
  [IsLocalField L₂]
  [Algebra K L₁]
  [FiniteDimensional K L₁]
  [IsGalois K L₁]
  [Algebra K L₂]
  [FiniteDimensional K L₂]
  [IsGalois K L₂]
  {f : L₁ →ₐ[K] L₂}
  {n : ℕ}
-- given
  (hK : IsNonarchimedeanLocalField K) :
-- imply
  HigherUnitsInNormGroup K L₂ hK n → HigherUnitsInNormGroup K L₁ hK n := by
-- proof
  intro h
  unfold HigherUnitsInNormGroup at *
  apply Set.Subset.trans h
  letI : Algebra L₁ L₂ := f.toRingHom.toAlgebra
  haveI : IsScalarTower K L₁ L₂ := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, AlgHom.commutes]
  haveI : FiniteDimensional L₁ L₂ := FiniteDimensional.right K L₁ L₂
  intro x hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨Algebra.norm L₁ a, by rw [Algebra.norm_norm]; exact ha⟩

end LocalConductor

namespace LocalConductor

/--
[finrank_ne_one_of_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean)
-/
@[path]
lemma finrank_ne_one_of_sub
  {K L₁ L₂ : Type*}
  [Field K]
  [Field L₁]
  [Field L₂]
  [Algebra K L₁]
  [FiniteDimensional K L₁]
  [Algebra K L₂]
  [FiniteDimensional K L₂]
  {f : L₁ →ₐ[K] L₂}
-- given
  (h : Module.finrank K L₁ ≠ 1) :
-- imply
  Module.finrank K L₂ ≠ 1 := by
-- proof
  intro h₂
  apply h
  have hf : Function.Injective f := f.toRingHom.injective
  have hle := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hf
  have hpos : 0 < Module.finrank K L₁ := Module.finrank_pos
  omega
end LocalConductor


namespace GlobalConductor

/--
[localConductorAtInfinitePlace_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean)
-/
@[path]
lemma localConductorAtInfinitePlace_le_one
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  {v : NumberField.InfinitePlace K} :
-- imply
  localConductorAtInfinitePlace K L v ≤ 1 := by
-- proof
  unfold localConductorAtInfinitePlace
  split_ifs <;> omega

end GlobalConductor

namespace GlobalConductor

/--
[localConductorAtInfinitePlace_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean)
-/
@[path]
lemma localConductorAtInfinitePlace_complex
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  {v : NumberField.InfinitePlace K}
-- given
  (hv : v.IsComplex) :
-- imply
  localConductorAtInfinitePlace K L v = 0 := by
-- proof
  unfold localConductorAtInfinitePlace
  simp only [ite_eq_left_iff]
  intro h
  exfalso
  apply h
  intro w hw
  rw [NumberField.InfinitePlace.isUnramified_iff]
  right
  rwa [hw]

end GlobalConductor

namespace GlobalConductor

/--
[finite_ramified_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean)
-/
@[path]
lemma finite_ramified_primes
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L] :
-- imply
  Set.Finite {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) | ¬ GlobalCFT.IsUnramifiedIn K L 𝔭} := by
-- proof
  letI : Algebra (FractionRing (NumberField.RingOfIntegers K))
    (FractionRing (NumberField.RingOfIntegers L)) :=
    FractionRing.liftAlgebra _ _
  letI : IsScalarTower (NumberField.RingOfIntegers K)
    (FractionRing (NumberField.RingOfIntegers K))
    (FractionRing (NumberField.RingOfIntegers L)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI : Algebra.IsSeparable (FractionRing (NumberField.RingOfIntegers K))
    (FractionRing (NumberField.RingOfIntegers L)) :=
    Algebra.IsSeparable.of_integral _ _
  have hdiff : differentIdeal (NumberField.RingOfIntegers K)
    (NumberField.RingOfIntegers L) ≠ ⊥ := differentIdeal_ne_bot
  have hfin_L := Ideal.finite_factors hdiff
  apply Set.Finite.subset (hfin_L.image
    (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K)))
  intro 𝔭 h𝔭
  simp only [Set.mem_setOf_eq, GlobalCFT.IsUnramifiedIn] at h𝔭
  push_neg at h𝔭
  obtain ⟨𝔔, h𝔔_prime, h𝔔_lies, h𝔔_ram⟩ := h𝔭
  haveI : 𝔔.IsPrime := h𝔔_prime
  haveI : 𝔔.LiesOver 𝔭.asIdeal := h𝔔_lies
  simp only [Set.mem_image, Set.mem_setOf_eq]
  have h𝔔_ne_bot : 𝔔 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot 𝔔
  refine ⟨⟨𝔔, h𝔔_prime, h𝔔_ne_bot⟩, ?_, ?_⟩
  ·
    exact dvd_differentIdeal_iff.mpr h𝔔_ram
  ·
    ext1
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.over_def 𝔔 𝔭.asIdeal]

end GlobalConductor

namespace GlobalConductor

/--
[localNormImage_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean)
-/
@[path]
lemma localNormImage_mono
  [Field K]
  [NumberField K]
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
  localNormImage K L₂ 𝔭 ⊆ localNormImage K L₁ 𝔭 := by
-- proof
  letI : Algebra L₁ L₂ := f.toRingHom.toAlgebra
  haveI : IsScalarTower K L₁ L₂ := IsScalarTower.of_algebraMap_eq fun x => by
    simp [RingHom.algebraMap_toAlgebra, AlgHom.commutes]
  haveI : FiniteDimensional L₁ L₂ := FiniteDimensional.right K L₁ L₂
  intro x hx
  simp only [localNormImage, Set.mem_iUnion] at hx ⊢
  obtain ⟨w₂, hw₂, a, ha⟩ := hx
  have hne : w₂.asIdeal.comap (algebraMap (𝓞 L₁) (𝓞 L₂)) ≠ ⊥ := by
    obtain ⟨y, hy_mem, hy_ne⟩ := (Submodule.ne_bot_iff _).mp w₂.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy_ne hy_mem
      (IsIntegralClosure.isIntegral (𝓞 L₁) L₂ y)
  set w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 L₁) :=
    ⟨w₂.asIdeal.comap (algebraMap (𝓞 L₁) (𝓞 L₂)),
      w₂.isPrime.comap _,
      hne⟩
  have hw₁ : w₁.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L₁)) = 𝔭.asIdeal := by
    show (w₂.asIdeal.comap (algebraMap (𝓞 L₁) (𝓞 L₂))).comap (algebraMap (𝓞 K) (𝓞 L₁)) =
      𝔭.asIdeal
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hw₂]
  have hw₂_over_w₁ : w₁.asIdeal ≤ w₂.asIdeal.comap (algebraMap (𝓞 L₁) (𝓞 L₂)) := le_refl _
  letI inst_bot : Algebra (𝔭.adicCompletion K) (w₁.adicCompletion L₁) :=
    HeightOneSpectrum.adicCompletionAlgebra w₁ 𝔭 (hw₁ ▸ le_refl _)
  letI inst_mid : Algebra (w₁.adicCompletion L₁) (w₂.adicCompletion L₂) :=
    HeightOneSpectrum.adicCompletionAlgebra w₂ w₁ hw₂_over_w₁
  letI inst_top : Algebra (𝔭.adicCompletion K) (w₂.adicCompletion L₂) :=
    HeightOneSpectrum.adicCompletionAlgebra w₂ 𝔭 (hw₂ ▸ le_refl _)
  haveI : IsScalarTower (𝔭.adicCompletion K) (w₁.adicCompletion L₁)
    (w₂.adicCompletion L₂) := by
    apply IsScalarTower.of_algebraMap_eq'
    have h_map_eq : @algebraMap (𝔭.adicCompletion K) (w₂.adicCompletion L₂) _ _ inst_top =
      (@algebraMap (w₁.adicCompletion L₁) (w₂.adicCompletion L₂) _ _ inst_mid).comp
        (@algebraMap (𝔭.adicCompletion K) (w₁.adicCompletion L₁) _ _ inst_bot) := by
      have h_dense : DenseRange (algebraMap K (𝔭.adicCompletion K)) :=
        𝔭.denseRange_algebraMap K
      set map_top := AdicCompletionAlgebra.adicCompletionMap (L := L₂) K 𝔭 w₂ (hw₂ ▸ le_refl _) with map_top_def
      set map_bot := AdicCompletionAlgebra.adicCompletionMap (L := L₁) K 𝔭 w₁ (hw₁ ▸ le_refl _) with map_bot_def
      set map_mid := AdicCompletionAlgebra.adicCompletionMap (L := L₂) L₁ w₁ w₂ hw₂_over_w₁ with map_mid_def
      have h_cont_top : Continuous map_top :=
        UniformSpace.Completion.continuous_extension
      have h_cont_bot : Continuous map_bot :=
        UniformSpace.Completion.continuous_extension
      have h_cont_mid : Continuous map_mid :=
        UniformSpace.Completion.continuous_extension
      have h_cont_comp : Continuous (map_mid.comp map_bot) :=
        h_cont_mid.comp h_cont_bot
      have h_agree : (map_top : 𝔭.adicCompletion K → w₂.adicCompletion L₂) ∘
        (algebraMap K (𝔭.adicCompletion K)) =
        (map_mid.comp map_bot : 𝔭.adicCompletion K → w₂.adicCompletion L₂) ∘
        (algebraMap K (𝔭.adicCompletion K)) := by
        ext k
        simp only [Function.comp_apply, RingHom.comp_apply]
        have h_lhs := RingHom.congr_fun (AdicCompletionAlgebra.adicCompletionMap_comp_algebraMap
          (L := L₂) K 𝔭 w₂ (hw₂ ▸ le_refl _)) k
        simp only [RingHom.comp_apply] at h_lhs
        have h_rhs1 := RingHom.congr_fun (AdicCompletionAlgebra.adicCompletionMap_comp_algebraMap
          (L := L₁) K 𝔭 w₁ (hw₁ ▸ le_refl _)) k
        simp only [RingHom.comp_apply] at h_rhs1
        have h_rhs2 := RingHom.congr_fun (AdicCompletionAlgebra.adicCompletionMap_comp_algebraMap
          (L := L₂) L₁ w₁ w₂ hw₂_over_w₁) (algebraMap K L₁ k)
        simp only [RingHom.comp_apply] at h_rhs2
        rw [h_lhs, h_rhs1, h_rhs2, IsScalarTower.algebraMap_apply K L₁ L₂]
      ext x
      exact congr_fun (h_dense.equalizer h_cont_top h_cont_comp h_agree) x
    exact h_map_eq
  haveI : Module.Free (𝔭.adicCompletion K) (w₁.adicCompletion L₁) :=
    Module.Free.of_divisionRing _ _
  haveI : Module.Free (w₁.adicCompletion L₁) (w₂.adicCompletion L₂) :=
    Module.Free.of_divisionRing _ _
  refine ⟨w₁, hw₁, Algebra.norm (w₁.adicCompletion L₁) a, ?_⟩
  rw [← ha]
  simp only [HeightOneSpectrum.localNormHom]
  exact @Algebra.norm_norm (𝔭.adicCompletion K) (w₁.adicCompletion L₁) _ _ _ _ (w₂.adicCompletion L₂) _ _ _ _ _ a

end GlobalConductor

namespace GlobalConductor

/--
[FinitePlaceHigherUnitsInNormGroup_of_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22Conductor.lean)
-/
@[path]
lemma FinitePlaceHigherUnitsInNormGroup_of_sub
  [Field K]
  [NumberField K]
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
  {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
  {n : ℕ} :
-- imply
  FinitePlaceHigherUnitsInNormGroup K L₂ 𝔭 n → FinitePlaceHigherUnitsInNormGroup K L₁ 𝔭 n := by
-- proof
  intro h
  exact Set.Subset.trans h (localNormImage_mono K L₁ L₂ f 𝔭)

end GlobalConductor


-- created on 2026-10-23
