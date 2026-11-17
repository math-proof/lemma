/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean -/

module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

@[expose] public section

/-!
# Elliptic functions
-/


namespace PeriodPair

/-- A function is lattice-periodic for `L` when every element of the lattice is a period. -/
def IsLatticePeriodic (L : PeriodPair) (f : ℂ → ℂ) : Prop :=
  ∀ ω : L.lattice, f.Periodic (ω : ℂ)

end PeriodPair
