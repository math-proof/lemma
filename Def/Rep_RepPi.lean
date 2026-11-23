module

public import Mathlib

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace Rep.RepPi

variable {k G : Type u} [CommRing k] [Group G] {ι : Type u} (F : ι → Rep.{u} k G)

noncomputable def piRepresentation : Representation k G ((i : ι) → F i) where
  toFun g := LinearMap.pi fun i => ((F i).ρ g).comp (LinearMap.proj i)
  map_one' := LinearMap.ext fun x => funext fun i => by simp
  map_mul' g h := LinearMap.ext fun x => funext fun i => by simp

noncomputable abbrev obj : Rep.{u} k G := Rep.of (piRepresentation F)

noncomputable def proj (i : ι) : obj F ⟶ F i := Rep.ofHom ⟨LinearMap.proj i, fun _ => rfl⟩

noncomputable def lift {X : Rep.{u} k G} (φ : (i : ι) → (X ⟶ F i)) : X ⟶ obj F :=
  Rep.ofHom ⟨LinearMap.pi fun i => (φ i).hom.toLinearMap, fun g => LinearMap.ext fun x => funext fun i =>
    Rep.hom_comm_apply (φ i) g x⟩

noncomputable def map {F' : ι → Rep.{u} k G} (φ : (i : ι) → (F i ⟶ F' i)) : obj F ⟶ obj F' :=
  lift F' fun i => proj F i ≫ φ i

end Rep.RepPi

end
