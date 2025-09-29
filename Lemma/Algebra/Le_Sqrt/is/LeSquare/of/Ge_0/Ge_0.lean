import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ≥ 0)
  (hy : y ≥ 0) :
-- imply
  x ≤ √y ↔ x ^ 2 ≤ y :=
-- proof
  Real.le_sqrt hx hy


-- created on 2025-08-02
