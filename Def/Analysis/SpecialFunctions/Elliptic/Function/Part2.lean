import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
/-!
# Elliptic functions
-/


namespace PeriodPair

/-- A function is lattice-periodic for `L` when every element of the lattice is a period. -/
def IsLatticePeriodic (L : PeriodPair) (f : ℂ → ℂ) : Prop :=
  ∀ ω : L.lattice, f.Periodic (ω : ℂ)

end PeriodPair
