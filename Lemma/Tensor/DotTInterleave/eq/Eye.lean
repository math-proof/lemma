import Lemma.Tensor.EqDot_Eye
import Lemma.Tensor.RotaryMatrix'0.eq.Eye
open Tensor


@[main]
private lemma main :
-- imply
  (interleave d)ᵀ @ interleave d = Tensor.eye (d + d) := by
-- proof
  apply Eq.symm
  apply Eq.trans RotaryMatrix'0.eq.Eye.symm
  apply Eq.trans (RotaryMatrix'.eq.DotDot_RotaryMatrix (0 : Tensor ℝ [d]))
  apply Eq.trans (congrArg (fun t : Tensor ℝ [d + d, d + d] => ((interleave d)ᵀ @ t) @ interleave d) RotaryMatrix0.eq.Eye)
  apply congrArg (fun t : Tensor ℝ [d + d, d + d] => t @ interleave d)
  apply EqDot_Eye


-- created on 2026-09-05
-- updated on 2026-09-06
