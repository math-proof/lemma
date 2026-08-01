import sympy.Basic


@[main]
private lemma main
  [SeminormedAddGroup α]
  {a : α} :
-- imply
  ‖a‖ ≥ 0 :=
-- proof
  norm_nonneg a


-- created on 2019-01-03
