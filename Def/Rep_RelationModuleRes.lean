module

public import Mathlib
public import Def.Rep_RelationModule

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G G' : Type u} [CommRing k] [Group G] [Group G'] (π : G' →* G)

def freeResMap (B : Rep.{u} k G) : Rep.free k G' B ⟶ Rep.res π (Rep.free k G B) :=
  Rep.freeLift k G' (Rep.res π (Rep.free k G B)) (fun b : B => (Finsupp.single b (MonoidAlgebra.single (1 : G) (1 : k)) : Rep.free k G B))

def relationModule.resMap (B : Rep.{u} k G) : relationModule (Rep.res π B) ⟶ Rep.res π (relationModule B) :=
  Rep.ofHom ⟨LinearMap.codRestrict _ ((freeResMap π B).hom.toLinearMap ∘ₗ (Submodule.subtype _)) (fun x => by
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        Representation.IntertwiningMap.toLinearMap_apply]
      rw [freeCover_freeResMap_apply]
      exact x.2),
    fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply (freeResMap π B) g (x : Rep.free k G' B))⟩

def resIhom (R X : Rep.{u} k G) : Rep.res π ((ihom R).obj X) ⟶ (ihom (Rep.res π R)).obj (Rep.res π X) :=
  Rep.ofHom ⟨LinearMap.id, fun g => LinearMap.ext fun f => by
      change ((ihom R).obj X).ρ (π g) f = ((ihom (Rep.res π R)).obj (Rep.res π X)).ρ g f
      erw [Rep.ihom_obj_ρ_apply, Rep.ihom_obj_ρ_apply]
      simp [map_inv]
      rfl⟩

section Int

variable {H H' : Type} [Group H] [Group H'] (ϖ : H' →* H)

def relationModuleInt.resMap (B : Rep ℤ H) : relationModuleInt (Rep.res ϖ B) ⟶ Rep.res ϖ (relationModuleInt B) :=
  Rep.ofHom ⟨((relationModule.resMap ϖ B).hom.toLinearMap.toAddMonoidHom).toIntLinearMap,
    fun g => LinearMap.ext fun x =>
      (Rep.hom_comm_apply (relationModule.resMap ϖ B) g (show relationModule (Rep.res ϖ B) from x))⟩

end Int

end Rep

end

end
