/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ResidueClassPsi.lean -/

import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The Chebyshev psi function in a residue class

This file defines the von Mangoldt sum over one residue class, using the same
inclusive real cutoff convention as `Chebyshev.psi`.
-/

namespace Chebyshev

/-- The von Mangoldt sum over positive integers at most `x` in the residue class `a`. -/
noncomputable def psiResidueClass {q : ℕ} (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt.residueClass a n
end Chebyshev
