import Mathlib.Algebra.Group.Basic
import sympy.Basic


@[main]
private lemma main
  {α : Type*} [AddCommGroup α]
  {x a y : α}
  -- given
  (h : x + a = y)
  -- imply
  : x = y - a := by
  -- proof
  calc
    x = x + a - a := by simp
    _ = y - a := by rw [h]

-- created on 2022-04-01
