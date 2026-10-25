import Mathlib
import Instance.Compat_Mathlib430

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

section Augmentation

variable (k G : Type u) [CommRing k] [Group G]

abbrev augε : Rep.leftRegularFinsupp k G ⟶ Rep.trivial k G k :=
  Rep.leftRegularHomFinsupp (Rep.trivial k G k) (1 : k)

abbrev augIdeal : Rep k G :=
  Rep.of (Representation.subrepresentation (Rep.leftRegularFinsupp k G).ρ
    (LinearMap.ker (augε k G).hom.toLinearMap) fun g x hx => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hx ⊢
      rw [Rep.hom_comm_apply, hx, map_zero])

abbrev augIdealι : augIdeal k G ⟶ Rep.leftRegularFinsupp k G :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

end Augmentation

section Splitting

variable {k G : Type u} [CommRing k] [Group G] (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C)

end Splitting

end Rep

end
