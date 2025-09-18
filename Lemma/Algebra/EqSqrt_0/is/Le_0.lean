import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ) :
-- imply
  √x = 0 ↔ x ≤ 0 :=
-- proof
  Real.sqrt_eq_zero'


-- created on 2025-01-17
