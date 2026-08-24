import Lemma.Real.CosSub.eq.AddCosCos_SinSin
open Real


@[main, comm]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.cos (x - y) = Real.sin x * Real.sin y + Real.cos x * Real.cos y := by
-- proof
  rw [CosSub.eq.AddCosCos_SinSin]
  ring


-- created on 2020-11-19
-- updated on 2026-08-23
