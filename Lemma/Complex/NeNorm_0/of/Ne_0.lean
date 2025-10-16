import Lemma.Complex.Eq_0.of.EqNorm_0
open Complex


@[main]
private lemma main
  {a : ℂ}
-- given
  (h : a ≠ 0) :
-- imply
  ‖a‖ ≠ 0 := by
-- proof
  by_contra h_Eq_0
  have := Eq_0.of.EqNorm_0 h_Eq_0
  contradiction


-- created on 2025-10-16
