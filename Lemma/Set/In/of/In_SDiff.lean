import sympy.Basic


@[main]
private lemma main
  {s U : Set α}
  {x : α}
-- given
  (h : x ∈ U \ s) :
-- imply
  x ∈ U :=
-- proof
  h.left


-- created on 2018-01-12
