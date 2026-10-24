/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Polynomial.lean -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Polynomial

/-!
# The p-adic valuation of an integer polynomial

For a nonzero polynomial over the integers, this file defines its `p`-adic valuation as the
minimum of the `p`-adic valuations of its nonzero coefficients.

The definition follows Itamar Nir, arXiv:2608.00668v1, line 419.
-/

/-- The minimum `p`-adic valuation of the nonzero coefficients of `f`. -/
@[nolint unusedArguments]
def padicValuation (p : ℕ) (_hp : Nat.Prime p) (f : Polynomial ℤ) (hf : f ≠ 0) : ℕ :=
  (f.support.image (fun n => padicValInt p (f.coeff n))).min'
    ((support_nonempty.mpr hf).image fun n => padicValInt p (f.coeff n))
end Polynomial
