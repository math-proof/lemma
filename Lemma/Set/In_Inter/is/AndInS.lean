import sympy.Basic


@[main]
private lemma main
  {e : α}
  {A B : Set α} :
-- imply
  e ∈ A ∩ B ↔ e ∈ A ∧ e ∈ B :=
-- proof
  Set.mem_inter_iff e A B


-- created on 2026-09-27
