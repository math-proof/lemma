import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e : α}
  {s S : Set α}
-- given
  (h : e ∈ s) :
-- imply
  e ∉ S \ s := by
-- proof
  intro hmem
  exact hmem.2 h


-- created on 2021-08-19
