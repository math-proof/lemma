/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean -/

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nullstellensatz
/-!
# Regularity of rational functions at a point

This file defines regularity of a fraction-ring element relative to a ring-homomorphism
that evaluates denominators. It also specializes the definition to affine coordinate rings.
-/


namespace FractionRing

variable {A K : Type*} [CommRing A] [CommRing K]

/-- A fraction is regular at an evaluation when some nonvanishing denominator clears it. -/
def IsRegularAt (ev : A →+* K) (r : FractionRing A) : Prop :=
  ∃ g : A, ev g ≠ 0 ∧
    algebraMap A (FractionRing A) g * r ∈
      Set.range (algebraMap A (FractionRing A))

end FractionRing
