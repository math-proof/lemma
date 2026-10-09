import sympy.Basic


/--
This lemma establishes that in a preorder, a strict inequality `x < y` implies the corresponding non-strict inequality `x ≤ y`.
It converts the strict order relation into a non-strict one, leveraging the properties of the preorder structure.
-/
@[path]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x ≤ y :=
-- proof
  le_of_lt h


@[path]
private lemma relax.given
  {x y : ℤ}
-- given
  (h : x < y + 1) :
-- imply
  x ≤ y := by
-- proof
  omega


-- created on 2018-12-29
-- updated on 2025-04-18
-- updated on 2026-09-27
