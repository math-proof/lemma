module

public import Mathlib

public section


public theorem Nat.Mul.of.Eq.left
  [Mul α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  d * x = d * y := by
-- proof
  rw [h]


public theorem Nat.Mul.of.Eq
  [Mul α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  x * d = y * d := by
-- proof
  rw [h]


-- created on 2019-05-02
