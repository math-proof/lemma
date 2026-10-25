import Mathlib
import Class.Patching_SystemTypes

set_option autoImplicit false

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

def IsCohenMacaulayOfDim (d : ℕ) : Prop :=
  ringKrullDim R = d ∧ Module.depth R R = d

end IsLocalRing
