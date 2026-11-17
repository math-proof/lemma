module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Def.Analysis.SpecialFunctions.Elliptic.ComplexMultiplication.Part2

/-!
# Complex multiplication of period lattices

This file defines the endomorphism ring of a complex period lattice.
-/

public section


namespace PeriodPair

@[simp]
theorem isProperIdeal_endomorphismRing (L : PeriodPair) :
    L.IsProperIdeal L.endomorphismRing :=
  rfl

end PeriodPair
