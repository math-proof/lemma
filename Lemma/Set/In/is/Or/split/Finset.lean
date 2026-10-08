import sympy.Basic


@[main]
private lemma main
  {x a b : α}
-- given
  (h : x ∈ ({a, b} : Set α)) :
-- imply
  x = a ∨ x = b := by
-- proof
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h


-- created on 2020-08-15
