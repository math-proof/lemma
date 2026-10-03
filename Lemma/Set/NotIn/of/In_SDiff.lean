import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e : α}
  {S s : Set α}
-- given
  (h : e ∈ S \ s) :
-- imply
  e ∉ s :=
-- proof
  h.right


-- created on 2026-10-03
