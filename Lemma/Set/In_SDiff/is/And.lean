import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e : α}
  {A B : Set α} :
-- imply
  e ∈ A \ B ↔ e ∈ A ∧ e ∉ B := by
-- proof
  exact Set.mem_sdiff e


-- created on 2026-09-27
