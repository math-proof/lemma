import Mathlib

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

theorem relationModule.ι_hom_apply (B : Rep.{u} k G) (x : relationModule B) :
    (relationModule.ι B).hom x = (x : Rep.free k G B) := rfl

theorem freeCover_hom_apply_ι (B : Rep.{u} k G) (x : relationModule B) :
    (freeCover B).hom ((relationModule.ι B).hom x) = 0 := x.2

abbrev relationSeq (B : Rep.{u} k G) : ShortComplex (Rep.{u} k G) where
  X₁ := relationModule B
  X₂ := Rep.free k G B
  X₃ := B
  f := relationModule.ι B
  g := freeCover B
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => x.2))

theorem relationSeq_X₁ (B : Rep.{u} k G) : (relationSeq B).X₁ = relationModule B := rfl
theorem relationSeq_X₂ (B : Rep.{u} k G) : (relationSeq B).X₂ = Rep.free k G B := rfl
theorem relationSeq_X₃ (B : Rep.{u} k G) : (relationSeq B).X₃ = B := rfl
theorem relationSeq_f (B : Rep.{u} k G) : (relationSeq B).f = relationModule.ι B := rfl
theorem relationSeq_g (B : Rep.{u} k G) : (relationSeq B).g = freeCover B := rfl

section Int

variable {G : Type} [Group G]

def relationCarrier (B : Rep ℤ G) : Type := relationModule B

instance relationCarrier.instAddCommGroup (B : Rep ℤ G) : AddCommGroup (relationCarrier B) :=
  inferInstanceAs (AddCommGroup (relationModule B))

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

theorem relationRepInt_apply (B : Rep ℤ G) (g : G) (x : relationCarrier B) :
    relationRepInt B g x = ((relationModule B).ρ g : relationModule B → relationModule B) x := rfl

abbrev relationModuleInt (B : Rep ℤ G) : Rep ℤ G := Rep.of (relationRepInt B)

def relationModuleInt.ι (B : Rep ℤ G) : relationModuleInt B ⟶ Rep.free ℤ G B :=
  Rep.ofHom ⟨((relationModule.ι B).hom.toLinearMap.toAddMonoidHom).toIntLinearMap, fun _ => rfl⟩

theorem relationModuleInt.ι_hom_apply (B : Rep ℤ G) (x : relationModuleInt B) :
    (relationModuleInt.ι B).hom x = (relationModule.ι B).hom (show relationModule B from x) := rfl

theorem relationModuleInt_ι_comp_freeCover (B : Rep ℤ G) : relationModuleInt.ι B ≫ freeCover B = 0 :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => freeCover_hom_apply_ι B (show relationModule B from x))

abbrev relationSeqInt (B : Rep ℤ G) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (relationModuleInt.ι B) (freeCover B) (relationModuleInt_ι_comp_freeCover B)

end Int

end Rep

end
