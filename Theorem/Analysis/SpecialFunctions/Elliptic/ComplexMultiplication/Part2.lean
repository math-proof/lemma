import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Def.Analysis.SpecialFunctions.Elliptic.ComplexMultiplication.Part2
/-!
# Complex multiplication of period lattices

This file defines the endomorphism ring of a complex period lattice.
-/


namespace PeriodPair

@[simp]
theorem isProperIdeal_endomorphismRing (L : PeriodPair) :
    L.IsProperIdeal L.endomorphismRing :=
  rfl

end PeriodPair
