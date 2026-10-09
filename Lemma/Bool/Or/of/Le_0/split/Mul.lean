import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x * y ≤ 0) :
-- imply
  (x ≥ 0 ∧ y ≤ 0) ∨ (x ≤ 0 ∧ y ≥ 0) :=
-- proof
  mul_nonpos_iff.mp h


-- created on 2019-05-30
