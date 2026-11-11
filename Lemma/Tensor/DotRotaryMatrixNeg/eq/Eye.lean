import Lemma.Tensor.DotT_RotaryMatrix.eq.Eye
import Lemma.Tensor.RotaryMatrixNeg.eq.TRotaryMatrix
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path]
private lemma main
-- given
  (α : Tensor ℝ [d]) :
-- imply
  (-α).rotaryMatrix ⬝ᵥ α.rotaryMatrix = Tensor.eye (d + d) := by
-- proof
  rw [RotaryMatrixNeg.eq.TRotaryMatrix]
  exact DotT_RotaryMatrix.eq.Eye α


-- created on 2026-09-03
-- updated on 2026-09-05
