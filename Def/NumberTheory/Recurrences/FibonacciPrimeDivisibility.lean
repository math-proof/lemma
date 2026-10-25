/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/FibonacciPrimeDivisibility.lean -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Dvd


namespace MetaMathlibExt

/-! # Fibonacci divisibility at `p - (5/p)`
-/

/-- Even part of `(1 + √5)^n`: `∑ k, C(n,2k) 5^k`. -/
def evenSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n (2 * k) : ℤ) * 5 ^ k

/-- Odd part of `(1 + √5)^n`: `∑ k, C(n,2k+1) 5^k`. -/
def oddSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n (2 * k + 1) : ℤ) * 5 ^ k

end MetaMathlibExt
