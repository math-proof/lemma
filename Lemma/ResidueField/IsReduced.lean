import Mathlib
import sympy.Basic
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma Ws33.RFF.mem_map_of_one_tmul_eq_zero {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [Algebra A B] (b : B) (hb : ((1 : ResidueField A) ⊗ₜ[A] b : ResidueField A ⊗[A] B) = 0) : b ∈ (maximalIdeal A).map (algebraMap A B) := by
  classical
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)
  have h1 : e (Ideal.Quotient.mk _ b) = (1 : ResidueField A) ⊗ₜ[A] b := Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk B (maximalIdeal A) b
  apply Ideal.Quotient.eq_zero_iff_mem.mp _
  apply e.injective
  rw [h1, map_zero]
  apply hb
/--
[IsReduced_tensorProduct_residueField_of_forall_isMaximal_adicCompletion](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsReduced_tensorProduct_residueField_of_forall_isMaximal_adicCompletion.lean)
-/
@[path]
private lemma main
  {A : Type} [CommRing A] [IsLocalRing A]
  {C : Type} [CommRing C] [Algebra A C] [IsNoetherianRing C]
  -- given
  (h : ∀ x : Ideal C, x.IsMaximal → (maximalIdeal A).map (algebraMap A C) ≤ x → IsReduced (ResidueField A ⊗[A] AdicCompletion x C)) :
  -- imply
  IsReduced (ResidueField A ⊗[A] C) := by
  -- proof
  classical
  let ι : C →+* ResidueField A ⊗[A] C := (Algebra.TensorProduct.includeRight : C →ₐ[A] ResidueField A ⊗[A] C).toRingHom
  have hιapp : ∀ c : C, ι c = (1 : ResidueField A) ⊗ₜ[A] c := fun c => rfl
  set K : Ideal C := (maximalIdeal A).map (algebraMap A C) with hK
  have hι : Function.Surjective ι := by
    intro s
    refine TensorProduct.inductionOn s ?_ ?_
    ·
      intro k c
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
      refine ⟨a • c, ?_⟩
      rw [hιapp, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      rfl
    ·
      intro x y hx hy
      obtain ⟨cx, rfl⟩ := hx
      obtain ⟨cy, rfl⟩ := hy
      exact ⟨cx + cy, map_add _ _ _⟩
  have hιA : ∀ a ∈ maximalIdeal A, ι (algebraMap A C a) = 0 := by
    intro a ha
    rw [hιapp, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    change IsLocalRing.residue A a ⊗ₜ[A] (1 : C) = 0
    rw [(IsLocalRing.residue_eq_zero_iff a).mpr ha, TensorProduct.zero_tmul]
  have hKι : K.map ι = ⊥ := by
    rw [hK, Ideal.map_map, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    apply hιA a ha
  let hNS : IsNoetherianRing (ResidueField A ⊗[A] C) := isNoetherianRing_of_surjective C _ ι hι
  refine ⟨fun s hs => ?_⟩
  obtain ⟨c, rfl⟩ := hι s
  obtain ⟨n, hn⟩ := hs
  have hcnK : c ^ n ∈ K := by
    have : ι (c ^ n) = 0 := by
      rw [map_pow]
      apply hn
    apply Ws33.RFF.mem_map_of_one_tmul_eq_zero (c ^ n) this
  have hmem : ∀ (𝔫 : Ideal (ResidueField A ⊗[A] C)), 𝔫.IsMaximal → ∀ m : ℕ, ι c ∈ 𝔫 ^ m := by
    intro 𝔫 h𝔫 m
    let _ := h𝔫
    set x : Ideal C := 𝔫.comap ι with hxdef
    have hx : x.IsMaximal := Ideal.comap_isMaximal_of_surjective ι hι
    have hxA : (maximalIdeal A).map (algebraMap A C) ≤ x := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      show ι (algebraMap A C a) ∈ 𝔫
      rw [hιA a ha]
      apply 𝔫.zero_mem
    let Cx := AdicCompletion x C
    let θ : C →+* ResidueField A ⊗[A] Cx := (Algebra.TensorProduct.includeRight : Cx →ₐ[A] ResidueField A ⊗[A] Cx).toRingHom.comp (algebraMap C Cx)
    have hθapp : ∀ c' : C, θ c' = (1 : ResidueField A) ⊗ₜ[A] (algebraMap C Cx c') := fun c' => rfl
    have hθA : ∀ a ∈ maximalIdeal A, θ (algebraMap A C a) = 0 := by
      intro a ha
      rw [hθapp, ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      change IsLocalRing.residue A a ⊗ₜ[A] (1 : Cx) = 0
      rw [(IsLocalRing.residue_eq_zero_iff a).mpr ha, TensorProduct.zero_tmul]
    have hθK : K ≤ RingHom.ker θ := by
      rw [hK, Ideal.map_le_iff_le_comap]
      intro a ha
      apply hθA a ha
    have hθc : θ c = 0 := by
      let _ := h x hx hxA
      have : IsNilpotent (θ c) := by
        refine ⟨n, ?_⟩
        rw [← map_pow]
        apply hθK hcnK
      apply this.eq_zero
    have hcompA : (algebraMap C Cx).comp (algebraMap A C) = algebraMap A Cx := RingHom.ext fun a => rfl
    have hcx : algebraMap C Cx c ∈ K.map (algebraMap C Cx) := by
      have hzero : (1 : ResidueField A) ⊗ₜ[A] algebraMap C Cx c = 0 := by
        rw [← hθapp]
        apply hθc
      have := Ws33.RFF.mem_map_of_one_tmul_eq_zero (algebraMap C Cx c) hzero
      rw [hK, Ideal.map_map, hcompA]
      apply this
    have hcm : c ∈ K ⊔ x ^ m := by
      have h1 : (AdicCompletion.evalₐ x m).toRingHom (algebraMap C Cx c) ∈ (K.map (algebraMap C Cx)).map (AdicCompletion.evalₐ x m).toRingHom := Ideal.mem_map_of_mem _ hcx
      have hcomp : (AdicCompletion.evalₐ x m).toRingHom.comp (algebraMap C Cx) = Ideal.Quotient.mk (x ^ m) := by
        ext c'
        show AdicCompletion.evalₐ x m (AdicCompletion.of x C (algebraMap C C c')) = Ideal.Quotient.mk (x ^ m) c'
        rw [AdicCompletion.evalₐ_of]
        rfl
      rw [Ideal.map_map, hcomp, show (AdicCompletion.evalₐ x m).toRingHom (algebraMap C Cx c) = Ideal.Quotient.mk (x ^ m) c from RingHom.congr_fun hcomp c] at h1
      obtain ⟨k, hk, hkc⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
      have hck : c - k ∈ x ^ m := by
        rw [← Ideal.Quotient.eq, eq_comm]
        apply hkc
      have : c = k + (c - k) := by ring
      rw [this]
      apply Submodule.add_mem_sup hk hck
    have : ι c ∈ (K ⊔ x ^ m).map ι := Ideal.mem_map_of_mem _ hcm
    rwa [Ideal.map_sup, hKι, bot_sup_eq, Ideal.map_pow, Ideal.map_comap_of_surjective ι hι] at this
  apply eq_zero_of_localization
  intro 𝔫 h𝔫
  let _ := h𝔫
  have hall : ∀ m : ℕ, algebraMap _ (Localization.AtPrime 𝔫) (ι c) ∈ (maximalIdeal (Localization.AtPrime 𝔫)) ^ m := by
    intro m
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    apply Ideal.mem_map_of_mem _ (hmem 𝔫 h𝔫 m)
  have hinf : algebraMap _ (Localization.AtPrime 𝔫) (ι c) ∈ ⨅ m : ℕ, (maximalIdeal (Localization.AtPrime 𝔫)) ^ m := Ideal.mem_iInf.mpr hall
  let _ : IsNoetherianRing (Localization.AtPrime 𝔫) := IsLocalization.isNoetherianRing 𝔫.primeCompl _ hNS
  have hbot : ⨅ m : ℕ, (maximalIdeal (Localization.AtPrime 𝔫)) ^ m = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing (R := Localization.AtPrime 𝔫) (I := maximalIdeal (Localization.AtPrime 𝔫)) (maximalIdeal.isMaximal _).ne_top
  rw [hbot, Ideal.mem_bot] at hinf
  apply hinf


-- created on 2026-10-20
