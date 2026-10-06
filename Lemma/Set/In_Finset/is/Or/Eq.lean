import sympy.Basic


@[main]
private lemma main
  {a b c e : α}
-- given
  (h : e ∈ ({a, b, c} : Set α)) :
-- imply
  e = a ∨ e = b ∨ e = c := by
-- proof
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h


-- created on 2023-05-30
