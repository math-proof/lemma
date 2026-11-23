module

public import Mathlib
public import Theorem.Rep.RelationModule

public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G G' : Type u} [CommRing k] [Group G] [Group G'] (π : G' →* G)


public theorem freeResMap_comp_resFunctor_map_freeCover (B : Rep.{u} k G) :
    freeResMap π B ≫ (Rep.resFunctor π).map (freeCover B) = freeCover (Rep.res π B) :=
  Rep.free_ext k G' _ _ _ (fun b => by simp [freeResMap, freeCover, Rep.resMap])


public theorem freeCover_freeResMap_apply (B : Rep.{u} k G) (x : Rep.free k G' B) :
    (freeCover B).hom ((freeResMap π B).hom x) = (freeCover (Rep.res π B)).hom x := by
  have h := congrArg (fun φ => φ.hom x) (freeResMap_comp_resFunctor_map_freeCover π B)
  simpa [Rep.resMap] using h


public theorem relationModule.resMap_hom_apply_coe (B : Rep.{u} k G) (x : relationModule (Rep.res π B)) :
    ((relationModule.resMap π B).hom x : Rep.free k G B) = (freeResMap π B).hom (x : Rep.free k G' B) := rfl


public theorem resIhom_hom_apply (R X : Rep.{u} k G) (f : Rep.res π ((ihom R).obj X)) :
    (resIhom π R X).hom f = (show (ihom (Rep.res π R)).obj (Rep.res π X) from f) := rfl

section Int

variable {H H' : Type} [Group H] [Group H'] (ϖ : H' →* H)


public theorem relationModuleInt.resMap_hom_apply (B : Rep ℤ H) (x : relationModuleInt (Rep.res ϖ B)) :
    (relationModuleInt.resMap ϖ B).hom x =
      (show Rep.res ϖ (relationModuleInt B) from
        (relationModule.resMap ϖ B).hom (show relationModule (Rep.res ϖ B) from x)) := rfl

end Int

end Rep

end
