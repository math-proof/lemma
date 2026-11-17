module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option autoImplicit false

def dedekindSaw (x : ℚ) : ℚ :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2


def dedekindSum (h : ℤ) (k : ℕ) : ℚ :=
  ∑ r ∈ Finset.range k, dedekindSaw ((r : ℚ) / k) * dedekindSaw ((h : ℚ) * r / k)
