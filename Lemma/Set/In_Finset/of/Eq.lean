import sympy.Basic


@[path]
private lemma main
  {x e : α}
-- given
  (h : x = e) :
-- imply
  x ∈ ({e} : Set α) := by
-- proof
  rw [h]
  apply Set.mem_singleton


-- created on 2018-10-23
