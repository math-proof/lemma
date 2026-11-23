/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean -/

module

public import Def.NumberTheory.PrimeInterval.Breusch.Grid
public import Theorem.Nat.PrimeInterval.Breusch.Grid
public import Theorem.Nat.PrimeInterval.Breusch.Lower
public import Theorem.Nat.PrimeInterval.Breusch.Theta
public import Def.NumberTheory.PrimeInterval.Breusch.Lower
public import Def.NumberTheory.PrimeInterval.Breusch.Theta
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Primorial
public import Mathlib.Computability.Reduce
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

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
