import Lemma.Real.CosAdd.eq.SubCosCos_SinSin
open Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : cos x = 0)
  (n : ℕ) :
-- imply
  cos (n * π + x) = 0 := by
-- proof
  rw [CosAdd.eq.SubCosCos_SinSin, h]
  simp


-- created on 2018-06-21
