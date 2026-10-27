import Notation.Data.Holor.Permute
import Lemma.Tensor.DotT.eq.RotaryMatrixSub
import Lemma.Tensor.RotaryMatrix0.eq.Eye
open Nat Tensor


@[path]
private lemma main
-- given
  (α : Tensor ℝ [d]) :
-- imply
  α.rotaryMatrixᵀ @ α.rotaryMatrix = Tensor.eye (d + d) := by
-- proof
  apply Eq.trans (DotT.eq.RotaryMatrixSub α α)
  rw [Sub.eq.Zero]
  exact RotaryMatrix0.eq.Eye


-- created on 2023-06-03
-- updated on 2026-10-26
