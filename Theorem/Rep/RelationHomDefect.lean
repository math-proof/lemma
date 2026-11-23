module

public import Mathlib
public import Theorem.Rep.RelationModule
public import Theorem.Rep.RelationModuleRes
public import Def.GroupCohomology_RepCokernel
public import Theorem.Rep.RepImage

public noncomputable section

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace Rep

section generalK

universe u

variable {k G : Type u} [CommRing k] [Group G]


public theorem preHom_hom_apply {A A' : Rep.{u} k G} (f : A ⟶ A') (E : Rep.{u} k G) (x : (ihom A').obj E) :
    (preHom f E).hom x = (show A' →ₗ[k] E from x) ∘ₗ f.hom.toLinearMap := rfl


public theorem preHom_comp {A A' A'' : Rep.{u} k G} (f : A ⟶ A') (f' : A' ⟶ A'') (E : Rep.{u} k G) :
    preHom f' E ≫ preHom f E = preHom (f ≫ f') E :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)


public theorem preHom_zero {A A' : Rep.{u} k G} (E : Rep.{u} k G) : preHom (0 : A ⟶ A') E = 0 :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => LinearMap.ext fun a => by
    change (show A' →ₗ[k] E from x) ((0 : A ⟶ A').hom a) = (0 : A →ₗ[k] E) a
    simp
    apply map_zero)

end generalK

section Int

variable {G : Type} [Group G] (B E : Rep ℤ G)


public theorem preCover_preι : preCover B E ≫ preι B E = 0 := by
  rw [preHom_comp, Rep.relationModuleInt_ι_comp_freeCover, preHom_zero]


