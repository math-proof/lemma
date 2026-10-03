import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : q → r) :
-- imply
  p ∧ q → r :=
-- proof
  fun hpq => h hpq.2


-- created on 2018-10-12
