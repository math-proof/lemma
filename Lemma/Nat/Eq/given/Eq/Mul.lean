import Mathlib.Algebra.Group.Basic
import sympy.Basic


@[main]
private lemma main
  {α : Type*} [Mul α]
  {x y c : α}
  -- given
  (h : x = y)
  -- imply
  : x * c = y * c := by
  -- proof
  rw [h]

-- created on 2023-11-06
