import sympy.Basic


/--
This lemma establishes that in a preorder, a strict inequality `x < y` implies the corresponding non-strict inequality `x ≤ y`.
It converts the strict order relation into a non-strict one, leveraging the properties of the preorder structure.
-/
@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x ≤ y :=
-- proof
  le_of_lt h


-- created on 2024-07-01
-- updated on 2025-04-18
