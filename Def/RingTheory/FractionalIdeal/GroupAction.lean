/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean -/

import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Pointwise
open scoped nonZeroDivisors
open scoped Pointwise

/-!
# Group actions on fractional ideals

This module constructs the action of a group of ring automorphisms on fractional
ideals of a fraction ring.
-/


namespace FractionalIdeal

variable (R K : Type*) [CommRing R] [IsDomain R] [CommRing K]
  [Algebra R K] [IsFractionRing R K]

/-- Ring automorphisms of `R` act on fractional ideals via `ringEquivOfRingEquiv`. -/
noncomputable def ringEquivOfRingEquivHom :
    RingAut R →* RingAut (FractionalIdeal R⁰ K) where
  toFun σ := FractionalIdeal.ringEquivOfRingEquiv K K σ
  map_one' := FractionalIdeal.ringEquivOfRingEquiv_refl K
  map_mul' σ τ := FractionalIdeal.ringEquivOfRingEquiv_trans K K K τ σ

end FractionalIdeal
