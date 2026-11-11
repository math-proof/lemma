import Notation.Data.Tensor.Permute
import Lemma.Tensor.DotT.eq.RotaryMatrix'Sub
import Instance.Data.Vector.Basic.Dot
open Nat Tensor


@[path]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  θ.rotaryMatrix'ᵀ ⬝ᵥ θ.rotaryMatrix' = Tensor.eye (d + d) := by
-- proof
  apply Eq.trans (DotT.eq.RotaryMatrix'Sub θ θ)
  rw [Sub.eq.Zero]
  exact RotaryMatrix'0.eq.Eye


-- created on 2023-06-03
