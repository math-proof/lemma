import Mathlib

set_option autoImplicit false

open CategoryTheory

namespace GroupCohomology.RepCokernel

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)

noncomputable abbrev obj : Rep.{u} k G :=
  Rep.of (Representation.quotient Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨a, rfl⟩
    exact ⟨X.ρ g a, Rep.hom_comm_apply f g a⟩)

end GroupCohomology.RepCokernel
