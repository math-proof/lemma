import sympy.Basic


@[path]
private lemma main
  {x a b c : α}
-- given
  (h : x ∈ ({a, b, c} : Set α)) :
-- imply
  x = a ∨ x = b ∨ x = c := by
-- proof
  simpa using h


-- created on 2021-06-11
