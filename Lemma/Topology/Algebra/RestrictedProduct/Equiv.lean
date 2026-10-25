import Mathlib
import Lemma.Topology.Algebra.RestrictedProduct.Basic
import Def.Mathlib_Topology_Algebra_RestrictedProduct_Equiv

section

open RestrictedProduct


section pi_congr_left

variable {ι₁ ι₂ : Type*}
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}


@[simp]
theorem Equiv.restrictedProductCongrLeft'_symm_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e)
    (x : Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) (j : ι₂) :
    (restrictedProductCongrLeft' e h).symm x (e.symm j) = x j := by
  simp [restrictedProductCongrLeft'_symm_apply]


@[simp]
theorem Equiv.restrictedProductCongrLeft_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (x : Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁]) (i : ι₁) :
    (restrictedProductCongrLeft e h) x (e i) = x i :=
  restrictedProductCongrLeft'_symm_apply_apply e.symm (𝓕₂.map_equiv_symm _ ▸ h) x _

end pi_congr_left

section pi_congr

variable {ι₁ ι₂ : Type*}
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}


@[simp]
theorem Equiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    e.restrictedProductCongr h φ hφ x (e i) =
      φ i (x i) := by
  simp [restrictedProductCongr]

@[simp]
theorem Equiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (e.restrictedProductCongr h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl

#adaptation_note /-- to_additive started failing in 4.28.0.
This should be fixed
in current mathlib; these lines to 200 can be deleted. See
https://github.com/ImperialCollegeLondon/FLT/pull/859/changes  -/


section ring_equiv

variable [(i : ι₁) → Semiring (R₁ i)] [(i : ι₂) → Semiring (R₂ i)]
  [(i : ι₁) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubsemiringClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}


@[simp]
theorem RingEquiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    RingEquiv.restrictedProductCongr e h φ hφ x (e i) =
      φ i (x i) := by
  simp [restrictedProductCongr]

@[simp]
theorem RingEquiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (RingEquiv.restrictedProductCongr e h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl

end ring_equiv

end pi_congr

section structure_map

variable {ι₁ ι₂ : Type*} {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
  {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂} {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

variable [(i : ι₁) → Ring (R₁ i)] [(i : ι₂) → Ring (R₂ i)]
  [(i : ι₁) → SubringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubringClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

theorem RingEquiv.restrictedProductCongr_bijOn_structureSubring (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+* R₂ (e i))
    (hφ : ∀ i, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    Set.BijOn (restrictedProductCongr e h φ (.of_forall hφ))
      (structureSubring R₁ A₁ 𝓕₁) (structureSubring R₂ A₂ 𝓕₂) := by
  have hm (i : _) := (hφ i).mapsTo
  have hs (i : _) := (hφ i).symm (φ i).toEquiv.invOn |>.mapsTo
  refine ⟨fun x hx ↦ ?_, (RingEquiv.injective _).injOn, fun y hy ↦ ?_⟩
  · refine mem_structureSubring_iff.2 fun i ↦ ?_
    obtain ⟨j, rfl⟩ := e.surjective i
    aesop
  · exact ⟨(restrictedProductCongr e h φ (.of_forall hφ)).symm y, by aesop⟩

end structure_map

section binary

variable {ι : Type*} {ℱ : Filter ι} {A B : ι → Type*}
  {C : (i : ι) → Set (A i)} {D : (i : ι) → Set (B i)}


lemma Equiv.restrictedProductProd_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductProd.symm ∘ Prod.map (inclusion _ _ hℱ) (inclusion _ _ hℱ) =
      inclusion (fun i ↦ A i × B i) (fun i ↦ C i ×ˢ D i) hℱ ∘ Equiv.restrictedProductProd.symm :=
  rfl

end binary

section pi

variable {ι : Type*} {ℱ : Filter ι} {n : Type*} [Fintype n]
    {A : n → ι → Type*}
    {C : (j : n) → (i : ι) → Set (A j i)}


lemma Equiv.restrictedProductPi_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductPi.symm ∘ Pi.map (fun i ↦ inclusion (A i) (C i) hℱ) =
      inclusion _ _ hℱ ∘ Equiv.restrictedProductPi.symm :=
  rfl

end pi

namespace RestrictedProduct

section flatten

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}
variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)


@[simp]
lemma flatten_apply (hf : Filter.Tendsto f ℱ 𝒢) (x) (i : ι) :
    flatten C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

variable (hf : Filter.comap f 𝒢 = ℱ)


@[simp]
lemma flatten_equiv_apply (x) (i : ι) :
    flatten_equiv C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_equiv C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)


@[simp]
lemma flatten_equiv'_apply (x) (i : ι) :
    flatten_equiv' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_equiv' C hf).symm x i j = x j.1 :=
  rfl

end flatten

end RestrictedProduct

end
