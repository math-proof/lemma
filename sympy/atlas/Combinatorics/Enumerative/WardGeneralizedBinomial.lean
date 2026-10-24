/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WardGeneralizedBinomial.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Ring.Nat

open scoped BigOperators

namespace MetaMathlibExt

/-!
# Ward generalized binomial coefficients

Source: T. Edgar and M. Z. Spivey, *Multiplicative Functions, Generalized Binomial
Coefficients, and Generalized Catalan Numbers*, Journal of Integer Sequences 19 (2016),
[`edgar3.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex).
-/

/-- The carry in the units place when adding `n` and `m` in base `b`.
Invalid bases `b ≤ 1` are totalized to zero. -/
def wardUnitsCarry (b n m : ℕ) : ℕ :=
  if 1 < b ∧ b ≤ n % b + m % b then 1 else 0

/-- Ward's product definition of a generalized binomial coefficient:
`{{n+m} choose n}_s = ∏_{b>1} s_b ^ ε₀^{b,n,m}`.

Only bases at most `n + m` can carry in the units place, so this is a finite product.
The source explicitly uses the product as a definition over arbitrary coefficient
sequences, including sequences with zero terms. -/
def wardGeneralizedBinomialCoefficient {R : Type*} [CommMonoid R]
    (s : ℕ → R) (n m : ℕ) : R :=
  ((Finset.range (n + m + 1)).filter fun b => 1 < b).prod
    fun b => s b ^ wardUnitsCarry b n m
end MetaMathlibExt
