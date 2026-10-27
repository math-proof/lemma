import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Def.Analysis.SpecialFunctions.Elliptic.ComplexMultiplication
/-!
# Complex multiplication of period lattices

This file defines the endomorphism ring of a complex period lattice.
-/


namespace PeriodPair

@[simp]
theorem mem_endomorphismRing {L : PeriodPair} {a : ℂ} :
    a ∈ L.endomorphismRing ↔ ∀ z ∈ L.lattice, a * z ∈ L.lattice :=
  Iff.rfl

end PeriodPair
