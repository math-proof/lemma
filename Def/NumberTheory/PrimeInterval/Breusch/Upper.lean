/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean -/

import Def.NumberTheory.PrimeInterval.Breusch.Grid
import Lemma.Nat.PrimeInterval.Breusch.Grid
import Lemma.Nat.PrimeInterval.Breusch.Lower
import Lemma.Nat.PrimeInterval.Breusch.Theta
import Def.NumberTheory.PrimeInterval.Breusch.Lower
import Def.NumberTheory.PrimeInterval.Breusch.Theta
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Computability.Reduce
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Breusch upper bound via the continuous `G`-function

The continuous `G9r` function, its identification with the grid `G9`, the `p`-adic
valuation identity for the weighted product, and the resulting upper bound
`logF9_upper` under the assumption that `(1890 * n, 2100 * n]` holds no prime.
-/


namespace MathlibExt.NumberTheory.BreuschWanted.Internal

open Nat Finset

/-- Continuous `G`-function: Möbius-weighted floors at real `x`. -/
noncomputable def G9r (x : ℝ) : ℤ := w9.toFinset.sum (fun q : ℕ × ℤ =>
  q.2 * ((Int.ofNat ⌊((10*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)
    - (Int.ofNat ⌊((9*Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊) - (Int.ofNat ⌊((Q9:ℕ):ℝ)*x/(q.1:ℝ)⌋₊)))

-- Single-factor valuation term.
/-- Single-factor `p`-adic valuation contribution. -/
def nu9term (q : ℕ × ℤ) (p n : ℕ) : ℤ :=
  q.2 * (((N10m q.1 n)!.factorization p : ℤ)
    - ((N9m q.1 n)!.factorization p : ℤ)
    - ((N1m q.1 n)!.factorization p : ℤ))

-- Total p-adic valuation of F(n).
/-- Total `p`-adic valuation of the weighted product `F_9(n)`. -/
def nu9 (p n : ℕ) : ℤ :=
  w9.toFinset.sum (fun q : ℕ × ℤ => nu9term q p n)

end MathlibExt.NumberTheory.BreuschWanted.Internal
