import Mathlib
import sympy.Basic
import Def.NumberTheory.NumberField.ExtensionDiscriminant.Part2
import Lemma.Nat.NumberField.ExtensionDiscriminant


/--
[discr_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean)
-/
@[path]
private lemma discr_smul {K L : Type*} [Field K] [Field L] [Algebra K L]
  (c : K) (b : Fin (Module.finrank K L) → L) :
  Algebra.discr K (fun i => c • b i) =
    c ^ (2 * Module.finrank K L) * Algebra.discr K b := by
  simp only [Algebra.discr_def]
  have hM : Algebra.traceMatrix K (fun i => c • b i) =
    c ^ 2 • Algebra.traceMatrix K b := by
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      Matrix.smul_apply, smul_eq_mul]
    rw [smul_mul_smul_comm]
    simp [map_smul, smul_eq_mul, sq]
  rw [hM, Matrix.det_smul]
  simp only [Fintype.card_fin]
  ring

/--
[image_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean)
-/
@[path]
private lemma image_subset (A : Type*) (L : Type u) (B SA SB : Type*)
  [CommRing A] [CommRing B] [CommRing SA] [CommRing SB] [Field L]
  [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
  [Algebra SA SB] [Algebra SB L] [Algebra SA L] [IsScalarTower SA SB L]
  [Algebra B SB] [IsScalarTower B SB L] :
  (imageOfB A L B : Set L) ⊆ (imageOfB SA L SB : Set L) := by
  intro x hx
  have hx' : x ∈ imageOfB A L B := hx
  rw [mem_imageOfB A L B] at hx'
  obtain ⟨b, rfl⟩ := hx'
  change algebraMap B L b ∈ imageOfB SA L SB
  rw [mem_imageOfB SA L SB]
  exact ⟨algebraMap B SB b, (IsScalarTower.algebraMap_apply B SB L b).symm⟩

/--
[discr_set_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean)
-/
@[path]
private lemma discr_set_subset (A K : Type*) (L : Type u) (B SA SB : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L] [CommRing SA] [CommRing SB]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L]
  [Algebra SA K] [Algebra SB L] [Algebra SA SB] [Algebra SA L]
  [IsScalarTower SA K L] [IsScalarTower SA SB L]
  [Algebra B SB] [IsScalarTower B SB L] :
  latticeDiscriminantSet A K (imageOfB A L B) ⊆
    latticeDiscriminantSet SA K (imageOfB SA L SB) := by
  intro d hd
  simp only [latticeDiscriminantSet, Set.mem_ofPred_eq] at hd ⊢
  obtain ⟨b, hb, rfl⟩ := hd
  refine ⟨b, fun i => SetLike.mem_coe.mp ?_, rfl⟩
  exact image_subset A L B SA SB (SetLike.mem_coe.mpr (hb i))
section Localization
variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [FiniteDimensional K L]
variable (S : Submonoid A)
variable (SA : Type*) [CommRing SA] [Algebra A SA] [IsLocalization S SA]
variable (SB : Type*) [CommRing SB] [Algebra B SB]
  [IsLocalization (Algebra.algebraMapSubmonoid B S) SB]
variable [Algebra SA K] [Algebra SB L] [Algebra SA SB] [Algebra SA L]
variable [IsScalarTower SA K L] [IsScalarTower SA SB L]
variable [IsScalarTower A SA K] [IsScalarTower B SB L]

/--
[extensionDiscriminant_localization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean)
-/
@[path]
lemma extensionDiscriminant_localization
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B] [CommRing SA] [Algebra A SA] [CommRing SB] [Algebra B SB] [Algebra SA K] [Algebra SA SB] [IsScalarTower A SA K]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L] [Algebra SB L] [Algebra SA L] [IsScalarTower SA K L] [IsScalarTower SA SB L] [IsScalarTower B SB L]
  {S : Submonoid A} [IsLocalization S SA] [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] :
-- imply
  Submodule.span SA (extensionDiscriminant A K L B : Set K) =
    extensionDiscriminant SA K L SB := by
-- proof
  rw [extensionDiscriminant_eq A K L B, extensionDiscriminant_eq SA K L SB]
  simp only [latticeDiscriminant]
  apply le_antisymm
  · rw [Submodule.span_span_of_tower]
    exact Submodule.span_mono (discr_set_subset A K L B SA SB)
  · apply Submodule.span_le.mpr
    intro d hd
    simp only [latticeDiscriminantSet, Set.mem_ofPred_eq] at hd
    obtain ⟨e, he, rfl⟩ := hd
    have hsb : ∀ i, ∃ sb : SB, algebraMap SB L sb = e i :=
      fun i => (mem_imageOfB SA L SB).mp (he i)
    choose sb hsb using hsb
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples
      (Algebra.algebraMapSubmonoid B S) Finset.univ sb
    choose bi hbi using fun i => ht i (Finset.mem_univ i)
    obtain ⟨a, haS, hat⟩ := Submonoid.mem_map.mp t.property
    have hL : ∀ i, algebraMap B L (bi i) = algebraMap A L a * e i := by
      intro i
      have h1 := congr_arg (algebraMap SB L) (hbi i)
      rw [← IsScalarTower.algebraMap_apply B SB L] at h1
      simp only [Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply B SB L] at h1
      rwa [hat.symm, ← IsScalarTower.algebraMap_apply A B L, hsb i] at h1
    have hsmul_mem : ∀ i, algebraMap A K a • e i ∈ imageOfB A L B := by
      intro i
      rw [mem_imageOfB A L B]
      refine ⟨bi i, ?_⟩
      rw [hL i, Algebra.smul_def, IsScalarTower.algebraMap_apply A K L]
    have hdisc_mem : Algebra.discr K (fun i => algebraMap A K a • e i) ∈
      extensionDiscriminant A K L B :=
      discr_mem_extensionDiscriminant A K L B hsmul_mem
    have hdisc_eq : Algebra.discr K (fun i => algebraMap A K a • e i) =
      (algebraMap A K a) ^ (2 * Module.finrank K L) * Algebra.discr K e :=
      discr_smul (algebraMap A K a) e
    have ha_unit : IsUnit (algebraMap A SA a) :=
      IsLocalization.map_units SA ⟨a, haS⟩
    have ha_ne : algebraMap A K a ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A SA K]
      exact (ha_unit.map (algebraMap SA K)).ne_zero
    have hdisc_inv : Algebra.discr K e =
      ((algebraMap A K a) ^ (2 * Module.finrank K L))⁻¹ *
        Algebra.discr K (fun i => algebraMap A K a • e i) := by
      rw [hdisc_eq]
      rw [inv_mul_cancel_left₀ (pow_ne_zero _ ha_ne)]
    obtain ⟨u, hu⟩ := ha_unit
    have hmap_inv : algebraMap SA K (↑(u⁻¹) : SA) = (algebraMap SA K (u : SA))⁻¹ :=
      eq_inv_of_mul_eq_one_right (by
        rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
    have hinv_eq : ((algebraMap A K a) ^ (2 * Module.finrank K L))⁻¹ =
      algebraMap SA K ((↑u⁻¹ : SA) ^ (2 * Module.finrank K L)) := by
      rw [map_pow, hmap_inv, ← inv_pow, hu,
        IsScalarTower.algebraMap_apply A SA K]
    rw [hdisc_inv, hinv_eq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (SetLike.mem_coe.mpr hdisc_mem))
end Localization


-- created on 2026-10-20
-- updated on 2026-10-23
