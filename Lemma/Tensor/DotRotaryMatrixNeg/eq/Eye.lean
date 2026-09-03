import Lemma.Tensor.DotT_RotaryMatrix.eq.Eye
import Lemma.Tensor.RotaryMatrixNeg.eq.TRotaryMatrix
open Tensor


@[main]
private lemma main
-- given
  (α : Tensor ℝ [d]) :
-- imply
  (rotaryMatrix (-α)) @ rotaryMatrix α = Tensor.eye (d + d) := by
-- proof
  rw [RotaryMatrixNeg.eq.TRotaryMatrix]
  exact DotT_RotaryMatrix.eq.Eye α


-- created on 2026-09-03
