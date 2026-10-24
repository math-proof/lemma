/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Theta.lean -/

import Mathlib.NumberTheory.Primorial
import Lemma.Nat.PrimeInterval.Breusch.ThetaBaseCases
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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
