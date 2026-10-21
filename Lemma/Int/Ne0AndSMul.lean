import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma FrobChareqEngine.engine3
    {K A V : Type*} [Field K] [CommRing A] [Algebra K A] [AddCommGroup V] [Module K V]
    [Module A V] [IsScalarTower K A V] [Module.Finite K V] [FaithfulSMul A V]
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ 𝔪, a • v = 0 := by
  classical
  have hinj : Function.Injective (Algebra.lsmul K K V : A →ₐ[K] Module.End K V) := by
    intro a b hab
    refine FaithfulSMul.eq_of_smul_eq_smul (α := V) fun v => ?_
    have := congrArg (fun f : Module.End K V => f v) hab
    simpa using this
  let _ : Module.Finite K A :=
    Module.Finite.of_injective (Algebra.lsmul K K V : A →ₐ[K] Module.End K V).toLinearMap hinj
  let _ : IsArtinianRing A := IsArtinianRing.of_finite K A
  let _ : IsNoetherianRing A := inferInstance
  let _ : Module.Finite A V := Module.Finite.of_restrictScalars_finite K A V
  have hann : Module.annihilator A V = ⊥ := by
    refine eq_bot_iff.mpr fun a ha => ?_
    rw [Module.mem_annihilator] at ha
    refine (Ideal.mem_bot).mpr (FaithfulSMul.eq_of_smul_eq_smul (α := V) fun v => ?_)
    rw [ha v, zero_smul]
  have hmin : 𝔪 ∈ (Module.annihilator A V).minimalPrimes := by
    rw [hann]
    refine ⟨⟨h𝔪.isPrime, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hle
    have hqmax : q.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal q).mp hq
    exact (hqmax.eq_of_le h𝔪.ne_top hle).ge
  have hass := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A V hmin
  change (⊥ : Submodule A V).IsAssociatedPrime 𝔪 at hass
  rw [Submodule.isAssociatedPrime_iff] at hass
  obtain ⟨-, x, hx⟩ := hass
  refine ⟨x, ?_, fun a ha => ?_⟩
  · rintro rfl
    apply h𝔪.ne_top
    rw [hx, eq_top_iff]
    intro a _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  · have : a ∈ (⊥ : Submodule A V).colon {x} := hx ▸ ha
    rw [Submodule.mem_colon_singleton] at this
    simpa using this
/--
[Module_exists_ne_zero_forall_smul_eq_smul_of_algHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_exists_ne_zero_forall_smul_eq_smul_of_algHom.lean)
-/
@[path]
private lemma main {K A V : Type*} [Field K] [CommRing A] [Algebra K A] [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V] [Module.Finite K V] [FaithfulSMul A V] (χ : A →ₐ[K] K) : ∃ v : V, v ≠ 0 ∧ ∀ a : A, a • v = χ a • v := by
  have hsurj : Function.Surjective χ := fun c => ⟨algebraMap K A c, χ.commutes c⟩
  have hmax : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hsurj
  obtain ⟨v, hv, hkill⟩ :=
    FrobChareqEngine.engine3 (K := K) (V := V) (RingHom.ker χ) hmax
  refine ⟨v, hv, fun a => ?_⟩
  have hmem : a - algebraMap K A (χ a) ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have := hkill _ hmem
  rw [sub_smul, sub_eq_zero, algebraMap_smul] at this
  exact this

-- created on 2026-10-20
