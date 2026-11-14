import Notation.Data.Tensor.Permute
import Lemma.Tensor.DotT.eq.RotaryMatrixSub
import Lemma.Tensor.RotaryMatrix0.eq.Eye
import Instance.Data.Vector.Basic.Dot
open Nat Tensor


@[path]
private lemma main
-- given
  (α : Tensor ℝ [d]) :
-- imply
  α.rotaryMatrixᵀ ⬝ᵥ α.rotaryMatrix = Tensor.eye (d + d) := by
-- proof
  apply Eq.trans (DotT.eq.RotaryMatrixSub α α)
  rw [Sub.eq.Zero]
  exact RotaryMatrix0.eq.Eye


-- created on 2023-06-16
-- updated on 2026-10-26
