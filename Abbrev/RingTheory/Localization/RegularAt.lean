/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean -/

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nullstellensatz
import Def.RingTheory.Localization.RegularAt
/-!
# Regularity of rational functions at a point

This file defines regularity of a fraction-ring element relative to a ring-homomorphism
that evaluates denominators. It also specializes the definition to affine coordinate rings.
-/


namespace MvPolynomial

/-- The affine coordinate ring of a set of `K`-points. -/
abbrev AffineCoordinateRing (X : Set (σ → K)) :=
  MvPolynomial σ K ⧸ vanishingIdeal K X

end MvPolynomial
