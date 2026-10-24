/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Dedekind psi function

This module defines the Dedekind psi function `dedekindPsi` by the prime-power product
`ψ(n) = ∏_{p ^ k ∥ n} p ^ (k - 1) * (p + 1)` for `n > 0`, with `ψ(0) = 0`. It proves
the prime-power formula, multiplicativity, and the rational product formula
`ψ(n) = n * ∏_{p ∣ n} (1 + 1 / p)`.
-/

namespace ArithmeticFunction

open Nat Finset

/-- The Dedekind psi function as an arithmetic function taking values in `ℕ`.

For `n = 0` the value is `0`, as required of an arithmetic function. For `n > 0`,
`dedekindPsi n = ∏_{p ^ k ∥ n} p ^ (k - 1) * (p + 1)`.
-/
def dedekindPsi : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun p k => p ^ (k - 1) * (p + 1)
  map_zero' := by simp
end ArithmeticFunction
