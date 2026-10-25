import Mathlib
import Class.Patching_SystemTypes
import Def.Patching_CohenMacaulayOfDim

set_option autoImplicit false

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]


namespace IsCohenMacaulayOfDim

variable {R} {d : ℕ}

lemma ringKrullDim_eq (h : IsCohenMacaulayOfDim R d) : ringKrullDim R = d := h.1

lemma depth_eq (h : IsCohenMacaulayOfDim R d) : Module.depth R R = d := h.2

end IsCohenMacaulayOfDim

end IsLocalRing
