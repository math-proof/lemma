import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Def.Analysis.SpecialFunctions.Elliptic.Function.Part2
/-!
# Elliptic functions
-/


namespace PeriodPair

/-- An elliptic function for `L` is a meromorphic lattice-periodic function. -/
structure IsEllipticFunction (L : PeriodPair) (f : ℂ → ℂ) : Prop where
  meromorphic : Meromorphic f
  periodic : L.IsLatticePeriodic f

end PeriodPair
