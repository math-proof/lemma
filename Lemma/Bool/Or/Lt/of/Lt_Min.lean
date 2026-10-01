import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y z : α}
-- given
  (h : min y z < x) :
-- imply
  y < x ∨ z < x :=
-- proof
  min_lt_iff.mp h


-- created on 2022-01-02
