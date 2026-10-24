/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Farey.lean -/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Rat

namespace Farey

/-!
# Farey sequences

Source: [Hamada, arXiv:2308.11999v6](https://arxiv.org/abs/2308.11999v6),
lines 283-290.
`F_n` is `a/b` with `0 ≤ a ≤ b ≤ n`, `gcd(a,b)=1`, ordered.
Consecutive elements are a Farey pair. Mediant is `(a+c)/(b+d)`.
-/

/-- Finite carrier of Farey fractions of order `n`. Enumerates all
`a/d` with `1 ≤ d ≤ n`, `0 ≤ a ≤ d`. Every `q` with `0 ≤ q ≤ 1`
and `q.den ≤ n` equals `q.num/q.den` with `0 ≤ q.num ≤ q.den`,
hence appears. -/
def fareyFinset (n : ℕ) : Finset ℚ :=
  ((Finset.Icc 1 n).biUnion fun d : ℕ =>
    ((Finset.Icc 0 d).image fun a : ℕ => ((a : ℤ) /. (d : ℤ) : ℚ)))

/-- The Farey sequence of order `n`, listed in increasing order. -/
def fareySeq (n : ℕ) : List ℚ :=
  (fareyFinset n).sort (· ≤ ·)

/-- Ordered Farey neighbor: consecutive in `F_n` with no intermediate
Farey fraction. -/
def IsFareyNeighbor (n : ℕ) (x y : ℚ) : Prop :=
  x ∈ fareyFinset n ∧ y ∈ fareyFinset n ∧ x < y ∧
  ∀ z ∈ fareyFinset n, ¬(x < z ∧ z < y)

/-- Canonical mediant `(a+c)/(b+d)` from reduced numerator/denominator data. -/
def mediant (x y : ℚ) : ℚ :=
  ((x.num + y.num) /. ((x.den + y.den : ℕ) : ℤ) : ℚ)
end Farey
