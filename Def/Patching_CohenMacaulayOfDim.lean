module

public import Mathlib
public import Class.Patching_SystemTypes

@[expose] public section

set_option autoImplicit false

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

def IsCohenMacaulayOfDim (d : ℕ) : Prop :=
  ringKrullDim R = d ∧ Module.depth R R = d

end IsLocalRing
