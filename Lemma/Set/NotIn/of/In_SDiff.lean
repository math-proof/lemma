import sympy.Basic


@[main]
private lemma main
  {s S : Set α}
  {e : α}
-- given
  (h : e ∈ S \ s) :
-- imply
  e ∉ s :=
-- proof
  h.right


-- created on 2018-01-13
