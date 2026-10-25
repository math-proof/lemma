import Mathlib
import Abbrev.GroupCohomology_RepCokernel

set_option autoImplicit false

open CategoryTheory

namespace GroupCohomology.RepImage

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)

noncomputable abbrev obj : Rep.{u} k G :=
  Rep.of (Representation.subrepresentation Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨x, rfl⟩
    exact ⟨X.ρ g x, Rep.hom_comm_apply f g x⟩)

end GroupCohomology.RepImage
