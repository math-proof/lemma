import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (e : α)
  (A B : Set α) :
-- imply
  e ∈ A ∩ B ↔ e ∈ A ∧ e ∈ B :=
-- proof
  Set.mem_inter_iff e A B


-- created on 2025-05-01
