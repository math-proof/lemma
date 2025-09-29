import sympy.Basic


/--
This lemma establishes that if an element `x` is less than `y` in a type with a less-than relation, then `y` is greater than `x`.
It provides a direct conversion between the two inequality forms, utilizing their inherent symmetry and definitional equivalence in the given algebraic structure.
-/
@[main]
private lemma main
  [LT α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  y > x := by
-- proof
  exact h


-- created on 2025-03-24
-- updated on 2025-04-04
