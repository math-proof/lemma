import Mathlib

set_option autoImplicit false

namespace TaylorWiles

variable {G Δ A : Type*} [Group G] [Group Δ] [CommRing A]

noncomputable def tameDescentChar (π : G →* Δ) (hπ : Function.Surjective π) (χ : G →* Aˣ)
    (hχ : ∀ g ∈ π.ker, χ g = 1) : Δ →* Aˣ :=
  (QuotientGroup.lift π.ker χ hχ).comp
    (MulEquiv.symm (QuotientGroup.quotientKerEquivOfSurjective π hπ) : Δ →* G ⧸ π.ker)

end TaylorWiles
