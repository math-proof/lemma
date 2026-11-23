module

public import Mathlib
public import Def.Rep_RelationModule
public import Def.Rep_RelationModuleRes
public import Def.GroupCohomology_RepCokernel
public import Def.Rep_RepImage

@[expose] public section

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace Rep

section generalK

universe u

variable {k G : Type u} [CommRing k] [Group G]

def preHom {A A' : Rep.{u} k G} (f : A ⟶ A') (E : Rep.{u} k G) : (ihom A').obj E ⟶ (ihom A).obj E :=
  Rep.ofHom ⟨LinearMap.lcomp k E f.hom.toLinearMap, fun g => LinearMap.ext fun x => by
    change (((ihom A').obj E).ρ g x) ∘ₗ f.hom.toLinearMap = ((ihom A).obj E).ρ g (x ∘ₗ f.hom.toLinearMap)
    erw [Rep.ihom_obj_ρ_apply, Rep.ihom_obj_ρ_apply]
    apply LinearMap.ext
    intro a
    simp only [LinearMap.coe_comp, Function.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Rep.hom_comm_apply]⟩

end generalK

section Int

variable {G : Type} [Group G] (B E : Rep ℤ G)

abbrev preCover : (ihom B).obj E ⟶ (ihom (Rep.free ℤ G B)).obj E := preHom (Rep.freeCover B) E

abbrev preι : (ihom (Rep.free ℤ G B)).obj E ⟶ (ihom (Rep.relationModuleInt B)).obj E := preHom (Rep.relationModuleInt.ι B) E

def homSeq₁ : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (preCover B E) (RepImage.toImage (preι B E))
    (Rep.hom_ext (DFunLike.ext _ _ fun x => Subtype.ext
      (congrArg (fun φ : (ihom B).obj E ⟶ (ihom (Rep.relationModuleInt B)).obj E => φ.hom x) (preCover_preι B E))))


end Int


end Rep

end

end
