import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_iso_comp_homOfLE_eq_homOfLE_comp_of_preimage_eq.lean)
-/
@[path]
private lemma main
    {Y Y' : Scheme.{u}} (V : Y.Opens) (V' : Y'.Opens) (φ : (V : Scheme.{u}) ≅ (V' : Scheme.{u}))
    (Z : Y.Opens) (Z' : Y'.Opens) (hZ : Z ≤ V) (hZ' : Z' ≤ V')
    (hφ : φ.hom ⁻¹ᵁ (V'.ι ⁻¹ᵁ Z') = V.ι ⁻¹ᵁ Z) :
    ∃ τ : (Z : Scheme.{u}) ≅ (Z' : Scheme.{u}),
      τ.hom ≫ Y'.homOfLE hZ' = Y.homOfLE hZ ≫ φ.hom ∧
      τ.inv ≫ Y.homOfLE hZ = Y'.homOfLE hZ' ≫ φ.inv := by
  have hsurj : Function.Surjective φ.hom.base := fun x => ⟨φ.inv.base x, Scheme.inv_hom_apply φ x⟩
  have hφset : φ.hom.base ⁻¹' (V'.ι.base ⁻¹' (Z' : Set Y')) = V.ι.base ⁻¹' (Z : Set Y) := by
    have h := congrArg (fun W : (↑V : Scheme.{u}).Opens => (W : Set (↑V : Scheme.{u}))) hφ
    simp only [Scheme.Hom.coe_preimage] at h
    exact h
  have hrangeLE : Set.range (Y.homOfLE hZ).base = V.ι.base ⁻¹' (Z : Set Y) := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      show V.ι.base ((Y.homOfLE hZ).base z) ∈ (Z : Set Y)
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      have : Z.ι.base z ∈ Set.range Z.ι.base := ⟨z, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    · intro hv
      have hv' : V.ι.base v ∈ Set.range Z.ι.base := by rw [Scheme.Opens.range_ι]; exact hv
      obtain ⟨z, hz⟩ := hv'
      refine ⟨z, Scheme.Hom.injective V.ι ?_⟩
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, hz]
  have hrange : Set.range (Y.homOfLE hZ ≫ φ.hom ≫ V'.ι).base = Set.range Z'.ι.base := by
    rw [Scheme.Opens.range_ι]
    have h1 : Set.range (Y.homOfLE hZ ≫ φ.hom ≫ V'.ι).base =
        V'.ι.base '' (φ.hom.base '' Set.range (Y.homOfLE hZ).base) := by
      ext y
      simp only [Set.mem_range, Set.mem_image, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨z, rfl⟩; exact ⟨_, ⟨_, ⟨z, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨_, ⟨z, rfl⟩, rfl⟩, rfl⟩; exact ⟨z, rfl⟩
    rw [h1, hrangeLE, ← hφset, Set.image_preimage_eq _ hsurj, Set.image_preimage_eq_inter_range,
      Scheme.Opens.range_ι]
    exact Set.inter_eq_left.mpr hZ'
  let _ : IsOpenImmersion (Y.homOfLE hZ ≫ φ.hom ≫ V'.ι) := inferInstance
  set τ := IsOpenImmersion.isoOfRangeEq (Y.homOfLE hZ ≫ φ.hom ≫ V'.ι) Z'.ι hrange with hτ
  have h1 : τ.hom ≫ Y'.homOfLE hZ' = Y.homOfLE hZ ≫ φ.hom := by
    rw [← cancel_mono V'.ι, Category.assoc, Scheme.homOfLE_ι, hτ, IsOpenImmersion.isoOfRangeEq_hom_fac,
      Category.assoc]
  refine ⟨τ, h1, ?_⟩
  rw [← cancel_epi τ.hom, Iso.hom_inv_id_assoc, ← Category.assoc, h1, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

-- created on 2026-10-20
