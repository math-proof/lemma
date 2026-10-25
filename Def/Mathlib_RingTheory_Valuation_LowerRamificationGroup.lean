import Mathlib
import Instance.Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option autoImplicit false

open scoped Pointwise


namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]


variable (R G) in

def lowerRamificationGroup (i : ℕ) : Subgroup G :=
  ((maximalIdeal R) ^ (i + 1)).inertia G

end IsLocalRing

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

def lowerRamificationGroup (A : ValuationSubring L) (i : ℕ) :
    Subgroup (A.decompositionSubgroup K) :=
  IsLocalRing.lowerRamificationGroup A (A.decompositionSubgroup K) i

end ValuationSubring
