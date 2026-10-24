import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens)

noncomputable def restrictPushforwardOpensIso :
    (Opens.map (g ∣_ W).base ⋙ (g ⁻¹ᵁ W).ι.opensFunctor : W.toScheme.Opens ⥤ X.Opens) ≅
      W.ι.opensFunctor ⋙ Opens.map g.base :=
  NatIso.ofComponents (fun U => eqToIso (image_morphismRestrict_preimage g W U))
    (fun _ => Subsingleton.elim _ _)

set_option maxHeartbeats 400000 in

noncomputable def pushforwardRestrictIso :
    restrictFunctor (g ⁻¹ᵁ W).ι ⋙ pushforward (g ∣_ W) ≅ pushforward g ⋙ restrictFunctor W.ι :=
  letI := CategoryTheory.Functor.isContinuous_comp.{u} (Opens.map (g ∣_ W).base) (g ⁻¹ᵁ W).ι.opensFunctor
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology ↑(g ⁻¹ᵁ W)) (Opens.grothendieckTopology X)
  letI := CategoryTheory.Functor.isContinuous_comp.{u} W.ι.opensFunctor (Opens.map g.base)
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  by
    refine SheafOfModules.pushforwardComp _ _ ≪≫
      SheafOfModules.pushforwardNatIso _ (restrictPushforwardOpensIso g W).symm ≪≫ ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
    refine SheafOfModules.pushforwardCongr ?_
    ext U x
    simp only [Functor.sheafPushforwardContinuous_obj_obj_obj, sheafCompose_obj_obj, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, Hom.toRingCatSheafHom, op_unop, Opens.ι_appIso, Iso.refl_inv,
      Functor.sheafPushforwardContinuousNatTrans, restrictPushforwardOpensIso, Iso.symm_hom, ObjectProperty.ι_obj,
      Category.assoc, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      TopCat.Presheaf.pushforward_obj_obj, Functor.sheafPushforwardContinuous_map_hom_app, Functor.op_obj,
      NatTrans.op_app, NatIso.ofComponents_inv_app, eqToIso.inv, eqToHom_op, Functor.comp_map, RingCat.hom_comp,
      CommRingCat.forgetToRingCat_map_hom]
    change (X.presheaf.map (eqToHom _)) ((g ∣_ W).app (unop U) x) = g.app (W.ι ''ᵁ unop U) x
    rw [morphismRestrict_app']
    erw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_eq_app]
    rfl

lemma pushforwardRestrictIso_hom_app_app (M : X.Modules) (U : W.toScheme.Opens) :
    ((pushforwardRestrictIso g W).hom.app M).app U =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage g W U).symm).op := by
  first
    | rfl
    | (ext x; simp [pushforwardRestrictIso, restrictPushforwardOpensIso, SheafOfModules.pushforwardCongr,
        SheafOfModules.pushforwardNatIso, SheafOfModules.pushforwardComp, eqToHom_op, Scheme.Modules.Hom.app])

end AlgebraicGeometry.Scheme.Modules
