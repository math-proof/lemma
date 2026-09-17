import Lemma.Nat.Sub.eq.Zero
import torch.Tensor.permute
import Lemma.Tensor.DotT.eq.RotaryMatrix'Sub
import Lemma.Tensor.RotaryMatrix'0.eq.Eye
open Nat Tensor


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  θ.rotaryMatrix'ᵀ @ θ.rotaryMatrix' = Tensor.eye (d + d) := by
-- proof
  apply Eq.trans (DotT.eq.RotaryMatrix'Sub θ θ)
  rw [Sub.eq.Zero]
  exact RotaryMatrix'0.eq.Eye


-- created on 2023-06-16
