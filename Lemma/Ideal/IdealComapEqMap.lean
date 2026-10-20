import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_Scheme_IdealSheafData_map_ideal_comap_specMap_eq_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_map_ideal_comap_specMap_eq_map.lean)
-/
@[path]
private lemma main
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (I : (Spec (CommRingCat.of A)).IdealSheafData) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
      ((I.comap (Spec.map (CommRingCat.ofHom φ))).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) =
      Ideal.map φ (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        (I.ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩)) := by
  set f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom φ) with hf
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp f.appTop.hom =
      φ.comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom := by
    have h2 := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
    exact h2
  have hmap : ∀ K : (Spec (CommRingCat.of B)).IdealSheafData,
      (K.map f).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ =
        (K.ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩).comap f.appTop.hom :=
    fun K ↦ Scheme.IdealSheafData.ideal_map_of_isAffineHom K f ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩
  set JA : Ideal (Γ(Spec (CommRingCat.of A), ⊤)) := I.ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ with hJA
  set JB : Ideal (Γ(Spec (CommRingCat.of B), ⊤)) := JA.map f.appTop.hom with hJB
  have hK : (Scheme.IdealSheafData.ofIdealTop JB).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ = JB := by
    simp
  apply le_antisymm
  ·
    have hle : I.comap f ≤ Scheme.IdealSheafData.ofIdealTop JB := by
      rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [hmap, hK]
      exact Ideal.le_comap_map
    have hle' := hle ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩
    rw [hK] at hle'
    refine (Ideal.map_mono hle').trans ?_
    rw [hJB, Ideal.map_map, hnat, ← Ideal.map_map]
  ·
    have hle : I ≤ (I.comap f).map f := Scheme.IdealSheafData.le_map_comap I f
    have hle' := hle ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩
    rw [hmap] at hle'
    have h2 : JB ≤ (I.comap f).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ := Ideal.map_le_iff_le_comap.mpr hle'
    have h3 := Ideal.map_mono (f := (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom) h2
    rw [hJB, Ideal.map_map, hnat, ← Ideal.map_map] at h3
    exact h3

-- created on 2026-10-20
