import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : α}
-- given
  (h : x = a) :
-- imply
  x ∈ ({a} : Set α) := by
-- proof
  rw [h, Set.mem_singleton_iff]


-- created on 2026-10-03
