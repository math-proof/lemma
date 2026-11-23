module

public import Mathlib

public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]


public theorem relationModule.ι_hom_apply (B : Rep.{u} k G) (x : relationModule B) :
    (relationModule.ι B).hom x = (x : Rep.free k G B) := rfl


public theorem freeCover_hom_apply_ι (B : Rep.{u} k G) (x : relationModule B) :
    (freeCover B).hom ((relationModule.ι B).hom x) = 0 := x.2


public theorem relationSeq_X₁ (B : Rep.{u} k G) : (relationSeq B).X₁ = relationModule B := rfl

public theorem relationSeq_X₂ (B : Rep.{u} k G) : (relationSeq B).X₂ = Rep.free k G B := rfl

public theorem relationSeq_X₃ (B : Rep.{u} k G) : (relationSeq B).X₃ = B := rfl

public theorem relationSeq_f (B : Rep.{u} k G) : (relationSeq B).f = relationModule.ι B := rfl

public theorem relationSeq_g (B : Rep.{u} k G) : (relationSeq B).g = freeCover B := rfl

section Int

variable {G : Type} [Group G]


public theorem relationRepInt_apply (B : Rep ℤ G) (g : G) (x : relationCarrier B) :
    relationRepInt B g x = ((relationModule B).ρ g : relationModule B → relationModule B) x := rfl


public theorem relationModuleInt.ι_hom_apply (B : Rep ℤ G) (x : relationModuleInt B) :
    (relationModuleInt.ι B).hom x = (relationModule.ι B).hom (show relationModule B from x) := rfl


public theorem relationModuleInt_ι_comp_freeCover (B : Rep ℤ G) : relationModuleInt.ι B ≫ freeCover B = 0 :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => freeCover_hom_apply_ι B (show relationModule B from x))

