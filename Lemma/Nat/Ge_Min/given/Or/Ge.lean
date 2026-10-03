import sympy.Basic


@[main]
private lemma main
  {x y z : ℤ}
-- given
  (h : x ≥ y ∨ x ≥ z) :
-- imply
  x ≥ min y z :=
-- proof
  min_le_iff.mpr h


-- created on 2022-01-02
