/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean -/

import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Group actions on fractional ideals

This module constructs the action of a group of ring automorphisms on fractional
ideals of a fraction ring.
-/

open scoped nonZeroDivisors
open scoped Pointwise

namespace FractionalIdeal

variable (R K : Type*) [CommRing R] [IsDomain R] [CommRing K]
  [Algebra R K] [IsFractionRing R K]

/-- Ring automorphisms of `R` act on fractional ideals via `ringEquivOfRingEquiv`. -/
noncomputable def ringEquivOfRingEquivHom :
    RingAut R →* RingAut (FractionalIdeal R⁰ K) where
  toFun σ := FractionalIdeal.ringEquivOfRingEquiv K K σ
  map_one' := FractionalIdeal.ringEquivOfRingEquiv_refl K
  map_mul' σ τ := FractionalIdeal.ringEquivOfRingEquiv_trans K K K τ σ

variable {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
  [CommRing K] [Algebra R K] [IsFractionRing R K]
  [MulSemiringAction G R]

/-- The `MulSemiringAction` on fractional ideals induced by that on the base ring. -/
noncomputable instance instMulSemiringAction :
    MulSemiringAction G (FractionalIdeal R⁰ K) :=
  MulSemiringAction.compHom _ ((ringEquivOfRingEquivHom R K).comp
    (MulSemiringAction.toRingAut G R))

/-- The induced multiplicative action on the group of invertible fractional ideals.

This is scoped to avoid the instance diamond documented for `Units.mulAction'`. -/
noncomputable abbrev unitsMulDistribMulAction :
    MulDistribMulAction G (FractionalIdeal R⁰ K)ˣ :=
  Units.mulDistribMulActionRight

scoped[FractionalIdealUnits] attribute [instance]
  FractionalIdeal.unitsMulDistribMulAction

open scoped FractionalIdealUnits
end FractionalIdeal
