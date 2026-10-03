import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e : α}
  {A B : Set α}
-- given
  (h : e ∈ A \ B) :
-- imply
  e ∈ A ∧ e ∉ B :=
-- proof
  h


-- created on 2026-10-03
