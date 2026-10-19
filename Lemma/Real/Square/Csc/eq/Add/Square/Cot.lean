import Lemma.Real.Square.Cot.eq.Sub.Square.Csc
open Real


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.sin x ≠ 0) :
-- imply
  Real.csc x ^ 2 = 1 + Real.cot x ^ 2 := by
-- proof
  linarith [Square.Cot.eq.Sub.Square.Csc h]


-- created on 2023-11-26
-- updated on 2026-10-17
