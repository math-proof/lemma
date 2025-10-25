import Lemma.Complex.Eq.of.EqReS.EqImS
open Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  z = re z + I * im z := by
-- proof
  apply Eq.of.EqReS.EqImS <;> simp


-- created on 2025-01-05
