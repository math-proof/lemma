/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/SigmaR.lean -/

/-
Copyright (c) 2026 Alex Kontorovich and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich and contributors, Adam Kiezun
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Misc
/-!
# Divisor sums with a complex exponent

This file defines the complex-exponent divisor sum as a complex-valued arithmetic function.

## Main definitions

* `ArithmeticFunction.sigmaR`

## Main statements

* `ArithmeticFunction.sigmaR_apply`
* `ArithmeticFunction.sigmaR_apply_one`
* `ArithmeticFunction.sigmaR_zero_apply`
* `ArithmeticFunction.sigmaR_natCast_apply`

## References

The definition follows the convention `σ_s(n) = ∑_{d ∣ n} d ^ s`. Its Lean representation is
adapted from the Apache-2.0 licensed `ArithmeticFunction.sigmaR` declaration in
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), revision
`be5e07e04cde20c5ceabf63759bd097a9c88173f`, in `PrimeNumberTheoremAnd.IwaniecKowalskiCh1`.
-/


namespace ArithmeticFunction

/-- The complex-valued arithmetic function `σ_s(n) = ∑_{d ∣ n} d ^ s`. -/
noncomputable def sigmaR (s : ℂ) : ArithmeticFunction ℂ where
  toFun := fun n => ∑ d ∈ n.divisors, (d : ℂ) ^ s
  map_zero' := by simp

end ArithmeticFunction
