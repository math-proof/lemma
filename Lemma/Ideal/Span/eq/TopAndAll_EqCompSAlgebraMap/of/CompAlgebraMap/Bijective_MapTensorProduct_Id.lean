import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


/--
[Algebra_exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct.lean)
-/
@[path]
private lemma main
  {𝒪 : Type u} [CommRing 𝒪]
  {𝒪' : Type u} [CommRing 𝒪'] [Algebra 𝒪 𝒪']
  {G : Type} [Group G] [Finite G]
  {S : Type u} [CommRing S]
  {τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪')} {s₁ s₂ : 𝒪' →+* S}
-- given
  (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
    Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
      (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
  (hs : s₁.comp (algebraMap 𝒪 𝒪') = s₂.comp (algebraMap 𝒪 𝒪')) :
-- imply
  ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ i : Fin k, ∃ σ : G,
    (algebraMap S (Localization.Away (r i))).comp s₂ =
      (algebraMap S (Localization.Away (r i))).comp (s₁.comp ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')) := by
-- proof
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Algebra 𝒪 S := (s₁.comp (algebraMap 𝒪 𝒪')).toAlgebra
  have halgS : ∀ r : 𝒪, algebraMap 𝒪 S r = s₁ (algebraMap 𝒪 𝒪' r) := fun _ => rfl
  let s₁' : 𝒪' →ₐ[𝒪] S :=
    { s₁ with
      commutes' := by
        intro r
        apply (halgS r).symm }
  have hc₂ : ∀ r : 𝒪, s₂ (algebraMap 𝒪 𝒪' r) = algebraMap 𝒪 S r := fun r => by
    rw [halgS]
    apply (RingHom.congr_fun hs r).symm
  let s₂' : 𝒪' →ₐ[𝒪] S :=
    { s₂ with
      commutes' := by
        intro r
        apply hc₂ r }
  let Φa : 𝒪' ⊗[𝒪] 𝒪' →ₐ[𝒪] (G → 𝒪') :=
    AlgHom.pi (fun σ => (Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪).comp
      (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪')))
  have hΦa : ∀ (x : 𝒪' ⊗[𝒪] 𝒪') (σ : G), Φa x σ =
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x) :=
    fun _ _ => rfl
  have hbij : Function.Bijective Φa := hgal
  let Φe : 𝒪' ⊗[𝒪] 𝒪' ≃ₐ[𝒪] (G → 𝒪') := AlgEquiv.ofBijective Φa hbij
  have hΦe_tmul : ∀ (a b : 𝒪') (σ : G), Φe (a ⊗ₜ b) σ = a * τ σ b := by
    intro a b σ
    show Φa (a ⊗ₜ b) σ = _
    rw [hΦa, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
    rfl
  let Θ : 𝒪' ⊗[𝒪] 𝒪' →ₐ[𝒪] S := Algebra.TensorProduct.productMap s₁' s₂'
  have hΘ : ∀ a b : 𝒪', Θ (a ⊗ₜ b) = s₁ a * s₂ b := fun a b =>
    Algebra.TensorProduct.productMap_apply_tmul _ _ a b
  let χ : (G → 𝒪') →ₐ[𝒪] S := Θ.comp (Φe.symm : (G → 𝒪') →ₐ[𝒪] 𝒪' ⊗[𝒪] 𝒪')
  have hχΦ : ∀ z, χ (Φe z) = Θ z := fun z => by
    show Θ (Φe.symm (Φe z)) = Θ z
    rw [AlgEquiv.symm_apply_apply]
  let e : G → S := fun σ => χ (Pi.single σ 1)
  have he_mul : ∀ σ σ' : G, σ ≠ σ' → e σ * e σ' = 0 := by
    intro σ σ' hne
    show χ (Pi.single σ 1) * χ (Pi.single σ' 1) = 0
    rw [← map_mul]
    have : (Pi.single σ (1 : 𝒪') : G → 𝒪') * Pi.single σ' 1 = 0 := by
      funext ρ
      if h : ρ = σ then
        subst h
        simp [hne]
      else
        simp [Pi.single_eq_of_ne h]
    rw [this, map_zero]
  have he_idem : ∀ σ : G, e σ * e σ = e σ := by
    intro σ
    show χ (Pi.single σ 1) * χ (Pi.single σ 1) = χ (Pi.single σ 1)
    rw [← map_mul]
    congr 1
    funext ρ
    if h : ρ = σ then
      subst h
      simp
    else
      simp [Pi.single_eq_of_ne h]
  have he_sum : ∑ σ : G, e σ = 1 := by
    show ∑ σ : G, χ (Pi.single σ 1) = 1
    have h := Finset.univ_sum_single (1 : G → 𝒪')
    simp only [Pi.one_apply] at h
    rw [← map_sum, h, map_one]
  have hconst : ∀ c : 𝒪', Φe (c ⊗ₜ 1) = fun _ => c := by
    intro c
    funext σ
    rw [hΦe_tmul, map_one, mul_one]
  have hχ_single : ∀ (σ : G) (c : 𝒪'), χ (Pi.single σ c) = s₁ c * e σ := by
    intro σ c
    have : (Pi.single σ c : G → 𝒪') = Φe (c ⊗ₜ 1) * Pi.single σ 1 := by
      rw [hconst]
      funext ρ
      if h : ρ = σ then
        subst h
        simp
      else
        simp [Pi.single_eq_of_ne h]
    show χ (Pi.single σ c) = s₁ c * χ (Pi.single σ 1)
    rw [this, map_mul, hχΦ, hΘ, map_one, mul_one]
  have hkey : ∀ y : 𝒪', s₂ y = ∑ σ : G, s₁ (τ σ y) * e σ := by
    intro y
    have h1 : s₂ y = Θ (1 ⊗ₜ y) := by
      rw [hΘ, map_one, one_mul]
    have h2 : Φe ((1 : 𝒪') ⊗ₜ y) = ∑ σ : G, (Pi.single σ (τ σ y) : G → 𝒪') := by
      rw [Finset.univ_sum_single (fun σ => τ σ y)]
      funext σ
      rw [hΦe_tmul, one_mul]
    rw [h1, ← hχΦ, h2, map_sum]
    apply Finset.sum_congr rfl fun σ _ => hχ_single σ _
  refine ⟨Fintype.card G, fun i => e ((Fintype.equivFin G).symm i), ?_, ?_⟩
  ·
    rw [Ideal.eq_top_iff_one, ← he_sum]
    refine Ideal.sum_mem _ fun σ _ => ?_
    apply Ideal.subset_span
    refine ⟨Fintype.equivFin G σ, ?_⟩
    show e ((Fintype.equivFin G).symm (Fintype.equivFin G σ)) = e σ
    rw [Equiv.symm_apply_apply]
  ·
    intro i
    refine ⟨(Fintype.equivFin G).symm i, ?_⟩
    set σ := (Fintype.equivFin G).symm i
    set L := Localization.Away (e σ)
    have hu : IsUnit (algebraMap S L (e σ)) := IsLocalization.Away.algebraMap_isUnit (e σ)
    have h1 : algebraMap S L (e σ) = 1 := by
      obtain ⟨u, hu'⟩ := hu
      have hid : algebraMap S L (e σ) * algebraMap S L (e σ) = algebraMap S L (e σ) := by
        rw [← map_mul, he_idem]
      rw [← hu'] at hid ⊢
      have := congrArg (fun z => (↑u⁻¹ : L) * z) hid
      simpa [← mul_assoc] using this
    have h0 : ∀ σ' : G, σ' ≠ σ → algebraMap S L (e σ') = 0 := by
      intro σ' hne
      have := congrArg (algebraMap S L) (he_mul σ' σ hne)
      rwa [map_mul, h1, mul_one, map_zero] at this
    apply RingHom.ext
    intro y
    show algebraMap S L (s₂ y) = algebraMap S L (s₁ ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') y))
    rw [hkey, map_sum, Finset.sum_eq_single σ]
    · rw [map_mul, h1, mul_one]
    ·
      intro σ' _ hne
      rw [map_mul, h0 σ' hne, mul_zero]
    ·
      intro h
      apply absurd (Finset.mem_univ σ) h


-- created on 2026-10-13
