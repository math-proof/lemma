import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (a x : α) :
-- imply
  x ∈ ({a} : Set α) ↔ x = a :=
-- proof
  Set.mem_singleton_iff


-- created on 2018-10-23
-- updated on 2026-08-21
