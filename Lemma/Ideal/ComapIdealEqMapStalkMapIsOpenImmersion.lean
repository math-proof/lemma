import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private noncomputable def G
  {X : (Scheme : Type (u + 1))} (I : X.IdealSheafData) (U : X.affineOpens) (y : X) (hy : y ∈ (U : X.Opens)) :
    Ideal (X.presheaf.stalk y) :=
  Ideal.map (X.presheaf.germ (U : X.Opens) y hy).hom (I.ideal U)

private lemma G_eq_of_le
  {X : (Scheme : Type (u + 1))} (I : X.IdealSheafData) {U W : X.affineOpens} (h : W ≤ U) (y : X)
  (hyW : y ∈ (W : X.Opens)) (hyU : y ∈ (U : X.Opens)) :
    G I W y hyW = G I U y hyU := by
  unfold G
  rw [← I.map_ideal h, Ideal.map_map, ← CommRingCat.hom_comp]
  erw [TopCat.Presheaf.germ_res]

private lemma G_eq
  {X : (Scheme : Type (u + 1))} (I : X.IdealSheafData) (U₁ U₂ : X.affineOpens) (y : X)
  (h₁ : y ∈ (U₁ : X.Opens)) (h₂ : y ∈ (U₂ : X.Opens)) :
    G I U₁ y h₁ = G I U₂ y h₂ := by
  obtain ⟨r, hle, hyr⟩ := U₁.2.exists_basicOpen_le ⟨y, h₂⟩ h₁
  have hW : IsAffineOpen (X.basicOpen r) := U₁.2.basicOpen r
  rw [← G_eq_of_le I (U := U₁) (W := ⟨X.basicOpen r, hW⟩) (X.basicOpen_le r) y hyr h₁, ← G_eq_of_le I (U := U₂) (W := ⟨X.basicOpen r, hW⟩) hle y hyr h₂]

private lemma G_comap
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) [IsOpenImmersion f] (I : Y.IdealSheafData)
  (U : X.affineOpens) (y : X) (hy : y ∈ (U : X.Opens)) :
    G (I.comap f) U y hy = Ideal.map (f.stalkMap y).hom (G I ⟨(Scheme.Hom.opensFunctor f).obj U, U.2.image_of_isOpenImmersion f⟩ (f.base y) ⟨y, hy, rfl⟩) := by
  unfold G
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have hci : Ideal.comap (f.appIso U).inv.hom (I.ideal ⟨(Scheme.Hom.opensFunctor f).obj U, U.2.image_of_isOpenImmersion f⟩) = Ideal.map (f.appIso U).hom.hom (I.ideal ⟨(Scheme.Hom.opensFunctor f).obj U, U.2.image_of_isOpenImmersion f⟩) := by
    have hhi : (f.appIso (U : X.Opens)).inv.hom.comp (f.appIso (U : X.Opens)).hom.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
    have hih : ∀ a, (f.appIso (U : X.Opens)).hom.hom ((f.appIso (U : X.Opens)).inv.hom a) = a := by
      intro a
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]
    apply le_antisymm
    ·
      intro a ha
      rw [Ideal.mem_comap] at ha
      rw [← hih a]
      apply Ideal.mem_map_of_mem _ ha
    · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hhi, Ideal.comap_id]
  rw [hci, Ideal.map_map, Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appIso_hom, Category.assoc]
  erw [TopCat.Presheaf.germ_res]
  rw [Scheme.Hom.germ_stalkMap]

private lemma map_le_map_iff_of_isIso
  {R S : (CommRingCat : Type (u + 1))} (φ : R ⟶ S) [IsIso φ] (A B : Ideal R) :
    Ideal.map φ.hom A ≤ Ideal.map φ.hom B ↔ A ≤ B := by
  constructor
  ·
    intro h
    have := Ideal.map_mono (f := (inv φ).hom) h
    rwa [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id, Ideal.map_id, Ideal.map_id] at this
  · apply Ideal.map_mono

/--
[AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_comap_ideal_eq_map_stalkMap_of_isOpenImmersion.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) [IsOpenImmersion f] (I : Y.IdealSheafData) (x : X)
  (U : Y.affineOpens) (hU : f.base x ∈ (U : Y.Opens)) (V : X.affineOpens) (hV : x ∈ (V : X.Opens)) :
    Ideal.map (X.presheaf.germ (V : X.Opens) x hV).hom ((I.comap f).ideal V) = Ideal.map (f.stalkMap x).hom (Ideal.map (Y.presheaf.germ (U : Y.Opens) (f.base x) hU).hom (I.ideal U)) := by
  change G (I.comap f) V x hV = Ideal.map (f.stalkMap x).hom (G I U (f.base x) hU)
  rw [G_comap f I V x hV, G_eq I ⟨(Scheme.Hom.opensFunctor f).obj V, V.2.image_of_isOpenImmersion f⟩ U (f.base x) ⟨x, hV, rfl⟩ hU]


-- created on 2026-10-20
