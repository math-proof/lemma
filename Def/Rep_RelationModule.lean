module

public import Mathlib

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

def freeCover (B : Rep.{u} k G) : Rep.free k G B ⟶ B :=
  Rep.freeLift k G B (fun b : B => b)

abbrev relationModule (B : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (Representation.subrepresentation (Rep.free k G B).ρ (LinearMap.ker (freeCover B).hom.toLinearMap) fun g x hx => by
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hx ⊢
    rw [Rep.hom_comm_apply, hx, map_zero])

def relationModule.ι (B : Rep.{u} k G) : relationModule B ⟶ Rep.free k G B :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

abbrev relationSeq (B : Rep.{u} k G) : ShortComplex (Rep.{u} k G) where
  X₁ := relationModule B
  X₂ := Rep.free k G B
  X₃ := B
  f := relationModule.ι B
  g := freeCover B
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))

section Int

variable {G : Type} [Group G]

abbrev relationCarrier (B : Rep ℤ G) : Type := relationModule B

def relationRepInt (B : Rep ℤ G) : Representation ℤ G (relationCarrier B) where
  toFun g := (((relationModule B).ρ g).toAddMonoidHom).toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    change ((relationModule B).ρ 1) x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change ((relationModule B).ρ (g * h)) x = ((relationModule B).ρ g) (((relationModule B).ρ h) x)
    rw [map_mul]
    rfl

abbrev relationModuleInt (B : Rep ℤ G) : Rep ℤ G := Rep.of (relationRepInt B)

def relationModuleInt.ι (B : Rep ℤ G) : relationModuleInt B ⟶ Rep.free ℤ G B :=
  Rep.ofHom ⟨((relationModule.ι B).hom.toLinearMap.toAddMonoidHom).toIntLinearMap, fun _ => rfl⟩

abbrev relationSeqInt (B : Rep ℤ G) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (relationModuleInt.ι B) (freeCover B) (relationModuleInt_ι_comp_freeCover B)

end Int

end Rep

end

end
