import Lemma.Complex.Eq.of.Re.Im
open Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  z = re z + I * im z := by
-- proof
  apply Eq.of.Re.Im <;> simp


-- created on 2018-03-11
