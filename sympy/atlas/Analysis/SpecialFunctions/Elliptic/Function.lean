/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean -/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Elliptic functions
-/

namespace PeriodPair

/-- A function is lattice-periodic for `L` when every element of the lattice is a period. -/
def IsLatticePeriodic (L : PeriodPair) (f : ℂ → ℂ) : Prop :=
  ∀ ω : L.lattice, f.Periodic (ω : ℂ)

/-- An elliptic function for `L` is a meromorphic lattice-periodic function. -/
structure IsEllipticFunction (L : PeriodPair) (f : ℂ → ℂ) : Prop where
  meromorphic : Meromorphic f
  periodic : L.IsLatticePeriodic f
end PeriodPair
