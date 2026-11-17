/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Localization/RegularAt.lean -/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nullstellensatz
public import Def.RingTheory.Localization.RegularAt
@[expose] public section

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
