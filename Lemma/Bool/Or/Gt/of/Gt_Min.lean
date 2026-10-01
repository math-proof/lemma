import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y z : α}
-- given
  (h : x > min y z) :
-- imply
  x > y ∨ x > z :=
-- proof
  min_lt_iff.mp h


-- created on 2022-01-02
