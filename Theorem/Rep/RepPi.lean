module

public import Mathlib

public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace Rep.RepPi

variable {k G : Type u} [CommRing k] [Group G] {ι : Type u} (F : ι → Rep.{u} k G)


@[simp] public theorem piRepresentation_apply (g : G) (x : (i : ι) → F i) (i : ι) :
    piRepresentation F g x i = (F i).ρ g (x i) := rfl


public theorem obj_rho_apply (g : G) (x : obj F) (i : ι) : (obj F).ρ g x i = (F i).ρ g (x i) := rfl


@[simp] public theorem proj_hom_apply (i : ι) (x : obj F) : (proj F i).hom x = x i := rfl


@[simp] public theorem lift_hom_apply {X : Rep.{u} k G} (φ : (i : ι) → (X ⟶ F i)) (x : X) (i : ι) : (lift F φ).hom x i = (φ i).hom x := rfl


public theorem lift_proj {X : Rep.{u} k G} (φ : (i : ι) → (X ⟶ F i)) (i : ι) : lift F φ ≫ proj F i = φ i :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))


public theorem hom_ext {X : Rep.{u} k G} {f g : X ⟶ obj F} (h : ∀ i, f ≫ proj F i = g ≫ proj F i) : f = g :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => funext fun i => by
    have := congrArg (fun ψ : X ⟶ F i => ψ.hom x) (h i)
    exact this))


@[simp] public theorem map_hom_apply {F' : ι → Rep.{u} k G} (φ : (i : ι) → (F i ⟶ F' i)) (x : obj F) (i : ι) :
    (map F φ).hom x i = (φ i).hom (x i) := rfl

end Rep.RepPi
