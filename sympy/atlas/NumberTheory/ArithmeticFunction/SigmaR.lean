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

/-- The defining finite divisor-sum formula for `sigmaR`. -/
theorem sigmaR_apply {n : ℕ} {s : ℂ} :
    sigmaR s n = ∑ d ∈ n.divisors, (d : ℂ) ^ s := by
  rfl

/-- Every complex-exponent divisor sum takes the value one at one. -/
@[simp]
theorem sigmaR_apply_one (s : ℂ) : sigmaR s 1 = 1 := by
  simp [sigmaR_apply]

/-- At exponent zero, `sigmaR` counts the divisors of its input. -/
@[simp]
theorem sigmaR_zero_apply (n : ℕ) :
    sigmaR 0 n = (n.divisors.card : ℂ) := by
  simp [sigmaR_apply]

/-- At a natural exponent, `sigmaR` agrees with Mathlib's divisor-power sum after coercion to
`ℂ`. -/
@[simp]
theorem sigmaR_natCast_apply (k n : ℕ) :
    sigmaR (k : ℂ) n = (sigma k n : ℂ) := by
  simp [sigmaR_apply, sigma_apply, Complex.cpow_natCast]

end ArithmeticFunction
