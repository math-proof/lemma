/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GibonacciNumber.lean -/

import Mathlib.Data.Nat.Fib.Basic

/-!
# Gibonacci numbers

This file formalizes the generalized Fibonacci sequence used by Dan Guyer and
aBa Mbirika, *GCD of Sums of k Consecutive Fibonacci, Lucas, and Generalized
Fibonacci Numbers*:
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Mbirika/mb5.tex>.
-/

namespace MetaMathlibExt

/-- The Gibonacci sequence with integer initial values `G₀` and `G₁`. -/
def gibonacciNumber (G₀ G₁ : ℤ) : ℕ → ℤ
  | 0 => G₀
  | 1 => G₁
  | n + 2 => gibonacciNumber G₀ G₁ (n + 1) + gibonacciNumber G₀ G₁ n
end MetaMathlibExt
