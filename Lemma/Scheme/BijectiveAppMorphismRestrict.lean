import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma bijective_app_congr
  {X B : (Scheme : Type (u + 1))} (p : X ⟶ B) {V W : B.Opens} (e : V = W)
  (h : Function.Bijective (p.app V)) :
  Function.Bijective (p.app W) := by
  subst e
  apply h
/--
[AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict.lean)
-/
@[path]
private lemma main
  {X B : (Scheme : Type (u + 1))} (p : X ⟶ B) (U : B.Opens)
  (h : Function.Bijective (morphismRestrict p U).appTop) :
  -- imply
  Function.Bijective (p.app U) := by
  -- proof
  apply bijective_app_congr p U.ι_image_top
  have key : p.app (U.ι ''ᵁ ⊤) =
      (morphismRestrict p U).appTop ≫ X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤).symm).op := by
    simp only [morphismRestrict_appTop, Category.assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id]
    rw [show X.presheaf.map (𝟙 _) = 𝟙 _ from X.presheaf.map_id _, Category.comp_id]
  rw [key]
  apply (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤).symm).op)).comp h


-- created on 2026-10-20
