import Lemma.Tensor.DotDot.eq.Dot_Dot
import torch.Tensor.permute
import Lemma.Tensor.DotT.eq.RotaryMatrix'Sub
import Lemma.Tensor.Dot_T.eq.Dot
open Tensor


@[main]
private lemma main
-- given
  (α β : Tensor ℝ [d])
  (q k : Tensor ℝ [d + d]) :
-- imply
  (α.rotaryMatrix' @ q) @ (β.rotaryMatrix' @ k) = q @ ((β - α).rotaryMatrix' @ k) := by
-- proof
  apply Eq.trans (congrArg (fun t => t @ (β.rotaryMatrix' @ k)) (Dot.eq.Dot_T q α.rotaryMatrix'))
  apply Eq.trans (DotDot.eq.Dot_Dot.vmv q α.rotaryMatrix'ᵀ (β.rotaryMatrix' @ k))
  apply congrArg (fun t => q @ t)
  apply Eq.trans (DotDot.eq.Dot_Dot.mmv α.rotaryMatrix'ᵀ β.rotaryMatrix' k).symm
  apply congrArg (fun t => t @ k) (DotT.eq.RotaryMatrix'Sub α β)


-- created on 2026-09-16
-- updated on 2026-09-16
