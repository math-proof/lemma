import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Theorem.Analysis.SpecialFunctions.Elliptic.ComplexMultiplication
/-!
# Complex multiplication of period lattices

This file defines the endomorphism ring of a complex period lattice.
-/


namespace PeriodPair

/-- A period lattice is a proper ideal of `𝒪` when its endomorphism ring is exactly `𝒪`.

The ambient assumptions that `𝒪` is an imaginary quadratic order and that the lattice is an
`𝒪`-ideal are deliberately kept separate from this predicate. -/
def IsProperIdeal (L : PeriodPair) (𝒪 : Subring ℂ) : Prop :=
  L.endomorphismRing = 𝒪

end PeriodPair
