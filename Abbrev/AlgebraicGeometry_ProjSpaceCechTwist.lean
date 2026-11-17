module

public import Mathlib

set_option autoImplicit false

@[expose] public noncomputable section

universe u

open Finset Function

namespace ProjSpaceCech

section Setup

variable (n : ℕ)

abbrev Twist.MonExp := Fin (n + 1) → ℤ

end Setup

section AltCech


end AltCech

section AltCech


end AltCech

section Cohomology


end Cohomology

end ProjSpaceCech

end
