import Mathlib
import Instance.Mathlib_RingTheory_LocalRing_Defs

set_option autoImplicit false

open Function IsLocalRing

variable (𝓞 : Type*) [CommRing 𝓞]

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]

class IsResidueAlgebra : Prop where
  isSurjective' : Surjective (algebraMap 𝓞 (𝓴 A))
