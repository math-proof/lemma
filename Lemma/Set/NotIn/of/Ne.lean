import sympy.Basic


@[main]
private lemma main
  {x y : α}
-- given
  (h : x ≠ y) :
-- imply
  x ∉ ({y} : Set α) := by
-- proof
  simp [h]


-- created on 2018-03-08
