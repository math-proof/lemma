import Lemma.Nat.Sub.eq.Zero
import Lemma.Tensor.DotT.eq.RotaryMatrixSub
import Lemma.Tensor.RotaryMatrix0.eq.Eye
open Nat Tensor


@[main]
private lemma main
-- given
  (α : Tensor ℝ [d]) :
-- imply
  (rotaryMatrix α)ᵀ @ (rotaryMatrix α) = Tensor.eye (d + d) := by
-- proof
  apply Eq.trans (DotT.eq.RotaryMatrixSub α α)
  rw [Sub.eq.Zero]
  exact RotaryMatrix0.eq.Eye


-- created on 2023-06-16
