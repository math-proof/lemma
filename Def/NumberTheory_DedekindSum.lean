import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

def dedekindSaw (x : ℚ) : ℚ :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2


def dedekindSum (h : ℤ) (k : ℕ) : ℚ :=
  ∑ r ∈ Finset.range k, dedekindSaw ((r : ℚ) / k) * dedekindSaw ((h : ℚ) * r / k)
