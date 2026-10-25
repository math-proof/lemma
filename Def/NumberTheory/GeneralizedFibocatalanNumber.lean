/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
/-!
Source: Killpatrick, JIS VOL 28, `killp6.tex`,
SHA256 `660c140f0fb7d3932abbea93631978efa4b1bf33bb089ba35a36a0556d5c40ec`.
Rank 340, lexical id `jis_term_14f7f012e4513e61c304514a`,
semantic id `jis_sem_959023b7307932f10fb8ebe4`.

Fibonacci-valued FiboCatalan generalization: Fibonacci factorial `F_n! `,
Jordan-type quotient `J_{r,F} = F_{2r+1}! / F_r! `, and the generalized
FiboCatalan number `J_{r,F} * F_{2n}! / (F_n! * F_{n+r+1}!)`.

Atomic scope here is the Fibonacci-valued case only. The Lucas-polynomial
analogue and the super FiboCatalan numbers are separate senses and out of
scope for this file.
-/


namespace MetaMathlibExt

section

/-- Fibonacci factorial: `F_n! = F_n * F_{n-1} * ... * F_2 * F_1`,
with the empty convention `F_0! = 1`. Values are in `ℚ` so the source
ratios are not distorted by `Nat` truncating division. Uses `Nat.fib`. -/
def fibonacciFactorial : ℕ → ℚ
  | 0 => 1
  | n + 1 => fibonacciFactorial n * (Nat.fib (n + 1) : ℚ)

/-- Jordan-type quotient `J_{r,F} = F_{2r+1}! / F_r! ` over `ℚ`. -/
def fibonacciJordanQuotient (r : ℕ) : ℚ :=
  fibonacciFactorial (2 * r + 1) / fibonacciFactorial r

/-- Generalized FiboCatalan number
`J_{r,F} * F_{2n}! / (F_n! * F_{n+r+1}!)` over `ℚ`. -/
def generalizedFibonacciCatalan (r n : ℕ) : ℚ :=
  fibonacciJordanQuotient r * fibonacciFactorial (2 * n) /
    (fibonacciFactorial n * fibonacciFactorial (n + r + 1))

/-- Nat-valued Fibonacci factorial: product of `fib (i+1)` for `i < N`. -/
def fibFactNat (N : ℕ) : ℕ := ∏ i ∈ Finset.range N, Nat.fib (i + 1)

end
end MetaMathlibExt
