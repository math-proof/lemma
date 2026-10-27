import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

universe u

/--
[AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp.lean)
-/
@[path]
private lemma main
  {Q Q' : Type u} [CommRing Q] [CommRing Q']
  {X X' : (Scheme : Type (u + 1))}
  (pr : X' ⟶ X)
  (U : X.Opens)
    (f : (↑U : (Scheme : Type (u + 1))) ⟶ Spec (CommRingCat.of Q))
    (hWU : ((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤)) = ((TopologicalSpace.Opens.map pr.base).obj U))
    (g : (↑(((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))) : (Scheme : Type (u + 1))) ⟶ Spec (CommRingCat.of Q')) (ψ : RingHom Q Q')
    (hfac : g ≫ Spec.map (CommRingCat.ofHom ψ) = (X'.isoOfEq hWU).hom ≫ (morphismRestrict pr U) ≫ f)
    (t : Q) (x' : ↥X') (hx' : x' ∈ ((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))) :
  ((Scheme.Opens.ι ((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))).stalkMap ⟨x', hx'⟩).hom ((X'.presheaf.germ (((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))) x' hx').hom ((pr.app ((Scheme.Hom.opensFunctor U.ι).obj ⊤)).hom ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t))))) = ((↑(((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))) : (Scheme : Type (u + 1))).presheaf.germ ⊤ ⟨x', hx'⟩ trivial).hom ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of Q')).inv.hom (ψ t))) := by
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of Q')).inv.hom (ψ t) =
      (Spec.map (CommRingCat.ofHom ψ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t) := by
    change (CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of Q')).inv).hom t = _
    rw [Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hR : (g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of Q')).inv.hom (ψ t)) =
      ((X'.isoOfEq hWU).hom ≫ (morphismRestrict pr U) ≫ f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t) := by
    rw [hnat, ← hfac]
    rfl
  have hL : (pr.app ((Scheme.Hom.opensFunctor U.ι).obj ⊤)).hom ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t))) =
      (pr.app ((Scheme.Hom.opensFunctor U.ι).obj ⊤)).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t)) := by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  rw [hR, hL]
  erw [Scheme.Hom.germ_stalkMap_apply]
  refine TopCat.Presheaf.germ_ext _ (((TopologicalSpace.Opens.map ((Scheme.Opens.ι ((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))).base))).obj (((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))))) hx' (𝟙 _) (homOfLE le_top) ?_
  set a := (pr.app ((Scheme.Hom.opensFunctor U.ι).obj ⊤)).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t)) with ha
  have hRHS : ((X'.isoOfEq hWU).hom ≫ (morphismRestrict pr U) ≫ f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t) =
      ((X'.isoOfEq hWU).hom.appTop).hom ((X'.presheaf.map (eqToHom (image_morphismRestrict_preimage pr U ⊤)).op).hom a) := by
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, morphismRestrict_appTop, ha]
    rfl
  rw [hRHS]
  simp only [Scheme.isoOfEq_hom, Scheme.homOfLE_appTop, Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map]
  rw [ha]
  have key : ∀ (b : X'.presheaf.obj (op (((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))))) {B C D : (TopologicalSpace.Opens ↥X')ᵒᵖ} (m : Opposite.op (((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))) ⟶ D) (e₁ : Opposite.op (((TopologicalSpace.Opens.map pr.base).obj ((Scheme.Hom.opensFunctor U.ι).obj ⊤))) ⟶ B) (h₁ : B ⟶ C) (k₁ : C ⟶ D), (X'.presheaf.map m).hom b = (X'.presheaf.map k₁).hom ((X'.presheaf.map h₁).hom ((X'.presheaf.map e₁).hom b)) := by
    intro b B C D m e₁ h₁ k₁
    have hm : m = e₁ ≫ h₁ ≫ k₁ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, hm]
  try exact key _ _ _ _ _
  all_goals erw [← CommRingCat.comp_apply, ← X'.presheaf.map_comp]
  all_goals exact key _ _ _ _ _

-- created on 2026-10-20
