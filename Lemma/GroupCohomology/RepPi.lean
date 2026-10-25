import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory

namespace GroupCohomology.RepPi

variable {k G : Type u} [CommRing k] [Group G] {ι : Type u} (F : ι → Rep.{u} k G)

noncomputable def piRepresentation : Representation k G ((i : ι) → F i) where
  toFun g := LinearMap.pi fun i => ((F i).ρ g).comp (LinearMap.proj i)
  map_one' := LinearMap.ext fun x => funext fun i => by simp
  map_mul' g h := LinearMap.ext fun x => funext fun i => by simp

@[simp] theorem piRepresentation_apply (g : G) (x : (i : ι) → F i) (i : ι) :
    piRepresentation F g x i = (F i).ρ g (x i) := rfl

noncomputable abbrev obj : Rep.{u} k G := Rep.of (piRepresentation F)

theorem obj_rho_apply (g : G) (x : obj F) (i : ι) : (obj F).ρ g x i = (F i).ρ g (x i) := rfl

noncomputable def proj (i : ι) : obj F ⟶ F i := Rep.ofHom ⟨LinearMap.proj i, fun _ => rfl⟩

@[simp] theorem proj_hom_apply (i : ι) (x : obj F) : (proj F i).hom x = x i := rfl

noncomputable def lift {X : Rep.{u} k G} (φ : (i : ι) → (X ⟶ F i)) : X ⟶ obj F :=
  Rep.ofHom ⟨LinearMap.pi fun i => (φ i).hom.toLinearMap, fun g => LinearMap.ext fun x => funext fun i =>
    Rep.hom_comm_apply (φ i) g x⟩

@[simp] theorem lift_hom_apply {X : Rep.{u} k G} (φ : (i : ι) → (X ⟶ F i)) (x : X) (i : ι) : (lift F φ).hom x i = (φ i).hom x := rfl

theorem lift_proj {X : Rep.{u} k G} (φ : (i : ι) → (X ⟶ F i)) (i : ι) : lift F φ ≫ proj F i = φ i :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

theorem hom_ext {X : Rep.{u} k G} {f g : X ⟶ obj F} (h : ∀ i, f ≫ proj F i = g ≫ proj F i) : f = g :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => funext fun i => by
    have := congrArg (fun ψ : X ⟶ F i => ψ.hom x) (h i)
    exact this))

noncomputable def map {F' : ι → Rep.{u} k G} (φ : (i : ι) → (F i ⟶ F' i)) : obj F ⟶ obj F' :=
  lift F' fun i => proj F i ≫ φ i

@[simp] theorem map_hom_apply {F' : ι → Rep.{u} k G} (φ : (i : ι) → (F i ⟶ F' i)) (x : obj F) (i : ι) :
    (map F φ).hom x i = (φ i).hom (x i) := rfl

end GroupCohomology.RepPi
