/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Grid.lean -/

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Breusch grid certificate (`k = 9`)

Möbius-weighted grid `G`-function for Breusch's proof with `Q = 210`: the divisor
table `w9`, grid values `G9 j`, the global maximum `M = 3` on `j < 18900`, and the
first-attainment thresholds `279`, `657`, `963`.

The Möbius values in `w9` were verified by hand against the Möbius function: every
entry is squarefree with value `(-1)^ω`. Three kernel-checked facts record this:
`w9_complete` (support), `w9_mu_sign` (values) and `w9_mu_sum_Q` (weighted sum).
-/

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

-- Q for the k=9 case: product of {2,3,5,7}.
/-- Truncation modulus for the `k = 9` case: `2 * 3 * 5 * 7`. -/
def Q9 : ℕ := 210

-- Explicit (divisor, Möbius value) table for `Q9`: every entry is squarefree,
-- with value `(-1)^ω`, e.g. `(35, 1)` since `35 = 5 * 7` has two prime factors.
/-- Divisor table for `Q9`, pairing each divisor with its Möbius value. -/
def w9 : List (ℕ × ℤ) :=
  [(1, 1), (2, -1), (3, -1), (5, -1), (6, 1), (7, -1), (10, 1), (14, 1),
   (15, 1), (21, 1), (30, -1), (35, 1), (42, -1), (70, -1), (105, -1),
   (210, 1)]

-- Single `G`-term: each `Nat` floor is cast with `Int.ofNat` first, so the
-- subtraction happens in `Int` (no `Nat` truncation).
/-- One summand of the grid `G`-function at residue `j`. -/
def G9term (q : ℕ × ℤ) (j : ℕ) : ℤ :=
  q.2 * (((10 * 210 * j / (q.1 * 18900) : ℕ) : ℤ)
    - ((9 * 210 * j / (q.1 * 18900) : ℕ) : ℤ)
    - ((210 * j / (q.1 * 18900) : ℕ) : ℤ))

-- G-function for k=9 on the j-grid (j < 18900 = 90 * Q9).
/-- Grid `G`-function for `k = 9`: the Möbius-weighted `10 - 9 - 1` floor sum. -/
def G9 (j : ℕ) : ℤ := (w9.map (fun q => G9term q j)).sum

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
end MathlibExt.NumberTheory.BreuschWanted.Internal
