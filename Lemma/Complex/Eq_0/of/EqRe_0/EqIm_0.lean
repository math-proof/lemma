import Lemma.Complex.Eq.of.EqReS.EqImS
open Complex


@[main]
private lemma main
  {z : ℂ}
-- given
  (h_Re : re z = 0)
  (h_Im : im z = 0) :
-- imply
  z = 0 := by
-- proof
  apply Eq.of.EqReS.EqImS <;>
  ·
    simp
    assumption


-- created on 2025-01-17
