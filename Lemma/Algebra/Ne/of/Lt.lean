import sympy.Basic


/--
This lemma converts a strict order relation `x < y` into a proof that `x` and `y` are distinct.
In a preorder, `x < y` inherently implies `x ≠ y`, and this lemma provides a direct way to extract the inequality from the strict order relation.
-/
@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x ≠ y :=
-- proof
  ne_of_lt h


-- created on 2024-07-01
-- updated on 2025-04-04
