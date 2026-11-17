module

public import Mathlib
public import Def.MvFormalGroup_BigWittLaw

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace MvFormalGroup

namespace BigWittLaw

open MvPolynomial

abbrev awt : ℕ → ℕ := fun m => m + 1

section OmegaInv

variable {A : Type*} [CommRing A] (t : A)

end OmegaInv

section Families

variable (R : Type u) [CommRing R]

end Families

end BigWittLaw

end MvFormalGroup

end
