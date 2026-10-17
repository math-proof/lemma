import Lemma.Real.Square.Tan.eq.Sub.Square.Sec
import sympy.Basic
open Real


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.cos x ≠ 0) :
-- imply
  Real.sec x ^ 2 = 1 + Real.tan x ^ 2 := by
-- proof
  linarith [Square.Tan.eq.Sub.Square.Sec h]


-- created on 2023-11-26
-- updated on 2026-10-17
