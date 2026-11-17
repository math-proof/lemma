/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/GroupAction.lean -/

module

public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Pointwise
public import Def.RingTheory.FractionalIdeal.GroupAction

@[expose] public section

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

/-- The `MulSemiringAction` on fractional ideals induced by that on the base ring. -/
noncomputable instance instMulSemiringAction :
    MulSemiringAction G (FractionalIdeal R⁰ K) :=
  MulSemiringAction.compHom _ ((ringEquivOfRingEquivHom R K).comp
    (MulSemiringAction.toRingAut G R))

end FractionalIdeal
