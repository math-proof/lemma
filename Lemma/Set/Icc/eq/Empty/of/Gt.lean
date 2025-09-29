import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  Icc x y = ∅ := by
-- proof
  aesop


-- created on 2025-08-03
