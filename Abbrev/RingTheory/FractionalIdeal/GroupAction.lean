/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean -/

import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Pointwise
import Instance.RingTheory.FractionalIdeal.GroupAction
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

variable {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
  [CommRing K] [Algebra R K] [IsFractionRing R K]
  [MulSemiringAction G R]

/-- The induced multiplicative action on the group of invertible fractional ideals.

This is scoped to avoid the instance diamond documented for `Units.mulAction'`. -/
noncomputable abbrev unitsMulDistribMulAction :
    MulDistribMulAction G (FractionalIdeal R⁰ K)ˣ :=
  Units.mulDistribMulActionRight

scoped[FractionalIdealUnits] attribute [instance]
  FractionalIdeal.unitsMulDistribMulAction

end FractionalIdeal
