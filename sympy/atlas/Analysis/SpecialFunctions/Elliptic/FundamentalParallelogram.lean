/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/FundamentalParallelogram.lean -/

import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Fundamental parallelograms of complex lattices
-/

namespace PeriodPair

/-- The fundamental parallelogram with vertex `α` spanned by the periods of `L`. -/
noncomputable def fundamentalParallelogram (L : PeriodPair) (α : ℂ) : Set ℂ :=
  (α + ·) '' ZSpan.fundamentalDomain L.basis
end PeriodPair
