import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma helper_main
  {G S : (Scheme : Type (u + 1))} (g : G ⟶ S)
  {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
  (s : Spec (CommRingCat.of k) ⟶ S) (ι : Spec (CommRingCat.of L) ⟶ G)
  (E : G ⟶ G) (hE : E ≫ g = g) (e : RingHom L L) (hι : Spec.map (CommRingCat.ofHom e) ≫ ι = ι ≫ E)
  (a : RingHom L A) (c : RingHom k A)
  (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s)
  (eA : RingHom A A) (hea : eA.comp a = a.comp e) (hec : eA.comp c = c) :
  -- imply
  Spec.map (CommRingCat.ofHom eA) ≫ pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq = pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq ≫ pullback.map g s g s E (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; apply hE.symm) (by rw [Category.comp_id, Category.id_comp]) := by
  -- proof
  have h1 : Spec.map (CommRingCat.ofHom eA) ≫ Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom e) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hea]
  have h2 : Spec.map (CommRingCat.ofHom eA) ≫ Spec.map (CommRingCat.ofHom c) = Spec.map (CommRingCat.ofHom c) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hec]
  apply pullback.hom_ext
  ·
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [← Category.assoc, h1, Category.assoc, hι]
  ·
    simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [h2]

/--
[AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp.lean)
-/
@[path]
private lemma main
  {G S : (Scheme : Type (u + 1))} (g : G ⟶ S)
  {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
  (s : Spec (CommRingCat.of k) ⟶ S) (ι : Spec (CommRingCat.of L) ⟶ G)
  (E : G ⟶ G) (hE : E ≫ g = g) (e : RingHom L L) (hι : Spec.map (CommRingCat.ofHom e) ≫ ι = ι ≫ E)
  (a : RingHom L A) (c : RingHom k A)
  (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s)
  (eA : RingHom A A) (hea : eA.comp a = a.comp e) (hec : eA.comp c = c) :
  -- imply
  Spec.map (CommRingCat.ofHom eA) ≫ pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq = pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq ≫ pullback.map g s g s E (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; apply hE.symm) (by rw [Category.comp_id, Category.id_comp]) :=
  helper_main g s ι E hE e hι a c hsq eA hea hec


-- created on 2026-10-20
