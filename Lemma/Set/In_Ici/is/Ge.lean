import sympy.sets.sets
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (x a : α) :
-- imply
  x ∈ Ici a ↔ x ≥ a :=
-- proof
  UpperSet.mem_Ici_iff


-- created on 2025-04-27
-- updated on 2025-08-02
