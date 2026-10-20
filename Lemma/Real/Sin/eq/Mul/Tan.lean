import Lemma.Real.Tan.eq.Div
open Real


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : Real.cos x ≠ 0) :
-- imply
  Real.sin x = Real.tan x * Real.cos x := by
-- proof
  rw [Tan.eq.Div]
  field_simp [h]


-- created on 2023-11-26
