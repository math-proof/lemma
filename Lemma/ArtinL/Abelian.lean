import Mathlib
import Instance.LanglandsTunnell_ArtinFrobenius
import Def.ArtinL_Abelian

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical

namespace ArtinL.Abelian

section Finite

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]


omit [NumberField M] [IsGalois K M] in
theorem ramificationGroup_zero (v : HeightOneSpectrum (𝓞 K)) :
    ramificationGroup K M v 0 = inertiaGroup K M v := by
  rw [ramificationGroup, zero_add, pow_one, inertiaGroup]

end Finite


section OfSubgroup

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]


theorem ofSubgroup_apply (H : Subgroup (F ≃ₐ[k] F)) (χ : H →* ℂˣ)
    (σ : F ≃ₐ[IntermediateField.fixedField H] F) :
    ofSubgroup H χ σ =
      χ ⟨σ.restrictScalars k,
        (IntermediateField.fixingSubgroup_fixedField H).le (fun x => σ.commutes x)⟩ :=
  rfl

omit [FiniteDimensional k F] in
theorem restrictScalars_fixingSubgroupEquiv (E : IntermediateField k F) (σ : E.fixingSubgroup) :
    (IntermediateField.fixingSubgroupEquiv E σ).restrictScalars k = σ := by
  ext; rfl

theorem ofSubgroup_fixingSubgroupEquiv (H : Subgroup (F ≃ₐ[k] F)) (χ : H →* ℂˣ) (h : H) :
    ofSubgroup H χ (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)
      ⟨h, by rw [IntermediateField.fixingSubgroup_fixedField H]; exact h.2⟩) = χ h := by
  rw [ofSubgroup, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

end OfSubgroup

section Basic

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

@[simp] theorem coeff_zero (ψ : (M ≃ₐ[K] M) →* ℂˣ) : coeff ψ 0 = 0 := by
  simp [coeff]

omit [IsGalois K M] in

theorem conductor_ne_bot (ψ : (M ≃ₐ[K] M) →* ℂˣ) : conductor ψ ≠ ⊥ := by
  unfold conductor
  refine finprod_induction (fun I : Ideal (𝓞 K) => I ≠ ⊥) ?_ (fun I J hI hJ => mul_ne_zero hI hJ)
    (fun v => pow_ne_zero _ v.ne_bot)
  exact one_ne_zero

omit [IsGalois K M] in

theorem absNorm_conductor_pos (ψ : (M ≃ₐ[K] M) →* ℂˣ) : 0 < Ideal.absNorm (conductor ψ) :=
  Nat.pos_of_ne_zero fun h => conductor_ne_bot ψ (Ideal.absNorm_eq_zero_iff.1 h)

omit [NumberField M] [IsGalois K M] in

theorem nPlus_le (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nPlus ψ ≤ nrRealPlaces K := by
  rw [nPlus, nrRealPlaces, ← Nat.card_eq_fintype_card]
  exact Nat.card_mono (Set.toFinite _) fun v hv => hv.1

omit [NumberField M] [IsGalois K M] in

theorem nPlus_add_nMinus (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nPlus ψ + nMinus ψ = nrRealPlaces K := by
  rw [nMinus, Nat.add_sub_cancel' (nPlus_le ψ)]

theorem norm_apply (ψ : (M ≃ₐ[K] M) →* ℂˣ) (σ : M ≃ₐ[K] M) : ‖((ψ σ : ℂˣ) : ℂ)‖ = 1 := by
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  obtain ⟨n, hn, hσ⟩ := hfin.exists_pow_eq_one
  have h1 : ((ψ σ : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hσ, map_one, Units.val_one]
  have h2 : ‖((ψ σ : ℂˣ) : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem coe_inv_apply (ψ : (M ≃ₐ[K] M) →* ℂˣ) (σ : M ≃ₐ[K] M) :
    ((ψ⁻¹ σ : ℂˣ) : ℂ) = starRingEnd ℂ ((ψ σ : ℂˣ) : ℂ) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact (Complex.inv_eq_conj (norm_apply ψ σ))

omit [NumberField M] [IsGalois K M] in
theorem isUnramifiedAt_inv_iff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    IsUnramifiedAt ψ⁻¹ v ↔ IsUnramifiedAt ψ v := by
  simp [IsUnramifiedAt]

theorem localValue_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    localValue ψ⁻¹ v = starRingEnd ℂ (localValue ψ v) := by
  unfold localValue
  rw [isUnramifiedAt_inv_iff]
  split_ifs
  · exact coe_inv_apply ψ _
  · simp

theorem idealValue_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (I : Ideal (𝓞 K)) :
    idealValue ψ⁻¹ I = starRingEnd ℂ (idealValue ψ I) := by
  unfold idealValue
  rw [show starRingEnd ℂ (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      localValue ψ v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) =
      (starRingAut (R := ℂ)).toMulEquiv (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      localValue ψ v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) from rfl,
    MulEquiv.map_finprod]
  exact finprod_congr fun v => by
    rw [localValue_inv, map_pow]
    rfl

omit [IsGalois K M] in
theorem swanConductor_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    swanConductor ψ⁻¹ v = swanConductor ψ v := by
  simp [swanConductor]

omit [IsGalois K M] in
theorem conductorExponent_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponent ψ⁻¹ v = conductorExponent ψ v := by
  rw [conductorExponent, conductorExponent, swanConductor_inv, isUnramifiedAt_inv_iff]

omit [IsGalois K M] in

theorem conductor_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) : conductor ψ⁻¹ = conductor ψ := by
  simp [conductor, conductorExponent_inv]

omit [NumberField K] [NumberField M] [IsGalois K M] in
theorem isPlusAt_inv_iff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : InfinitePlace K) :
    IsPlusAt ψ⁻¹ v ↔ IsPlusAt ψ v := by
  simp [IsPlusAt]

omit [NumberField M] [IsGalois K M] in
theorem nPlus_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nPlus ψ⁻¹ = nPlus ψ := by
  simp [nPlus, isPlusAt_inv_iff]

omit [NumberField M] [IsGalois K M] in
theorem nMinus_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nMinus ψ⁻¹ = nMinus ψ := by
  rw [nMinus, nMinus, nPlus_inv]

theorem coeff_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (n : ℕ) :
    coeff ψ⁻¹ n = starRingEnd ℂ (coeff ψ n) := by
  unfold coeff
  split_ifs
  · simp
  · rw [map_sum]
    exact Finset.sum_congr rfl fun I _ => idealValue_inv ψ I

end Basic

end ArtinL.Abelian

end
