/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Theta.lean -/

module

public import Mathlib.NumberTheory.Primorial
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Breusch primorial and logarithm bounds

The primorial estimate `primorial m ≤ 3.4 ^ m`, certified numerical bounds for
`log 2`, `log 5`, `log 3` and `log 17` with the resulting margin `13`, the
prime-counting bound `π(m) ≤ m / 3`, and gap positivity for `n ≥4762`.
-/


namespace MathlibExt.NumberTheory.BreuschWanted.Internal

open Nat Finset

-- M(t) = (6t)! / ((3t)! (2t)! t !), the multinomial for the 3.4 primorial bound.
/-- Multinomial `(6 * t)! / ((3 * t)! * (2 * t)! * t!)`. -/
def M34 (t : ℕ) : ℕ := (6*t)! / ((3*t)! * (2*t)! * t !)

end MathlibExt.NumberTheory.BreuschWanted.Internal
