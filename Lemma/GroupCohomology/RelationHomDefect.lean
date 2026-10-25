import Mathlib
import Lemma.GroupCohomology.RelationModule
import Lemma.GroupCohomology.RelationModuleRes
import Def.GroupCohomology_RepCokernel
import Lemma.GroupCohomology.RepImage

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

theorem preHom_hom_apply {A A' : Rep.{u} k G} (f : A ⟶ A') (E : Rep.{u} k G) (x : (ihom A').obj E) :
    (preHom f E).hom x = (show A' →ₗ[k] E from x) ∘ₗ f.hom.toLinearMap := rfl

theorem preHom_comp {A A' A'' : Rep.{u} k G} (f : A ⟶ A') (f' : A' ⟶ A'') (E : Rep.{u} k G) :
    preHom f' E ≫ preHom f E = preHom (f ≫ f') E :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

theorem preHom_zero {A A' : Rep.{u} k G} (E : Rep.{u} k G) : preHom (0 : A ⟶ A') E = 0 :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => LinearMap.ext fun a => by
    change (show A' →ₗ[k] E from x) ((0 : A ⟶ A').hom a) = (0 : A →ₗ[k] E) a
    simp)

end generalK

section Int

variable {G : Type} [Group G] (B E : Rep ℤ G)

abbrev preCover : (ihom B).obj E ⟶ (ihom (Rep.free ℤ G B)).obj E := preHom (Rep.freeCover B) E

abbrev preι : (ihom (Rep.free ℤ G B)).obj E ⟶ (ihom (Rep.relationModuleInt B)).obj E := preHom (Rep.relationModuleInt.ι B) E

theorem preCover_preι : preCover B E ≫ preι B E = 0 := by
  rw [preHom_comp, Rep.relationModuleInt_ι_comp_freeCover, preHom_zero]


def homSeq₁ : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (preCover B E) (GroupCohomology.RepImage.toImage (preι B E))
    (Rep.hom_ext (DFunLike.ext _ _ fun x => Subtype.ext
      (congrArg (fun φ : (ihom B).obj E ⟶ (ihom (Rep.relationModuleInt B)).obj E => φ.hom x) (preCover_preι B E))))


end Int

section Infl

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B E : Rep ℤ G) (E' : Rep ℤ G') (φ : Rep.res π E ⟶ E')


end Infl

end Rep

end
