import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  Icc x y = ∅ := by
-- proof
  aesop


-- created on 2021-04-30
