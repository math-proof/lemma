import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.DotT.eq.RotaryMatrixSub
import Lemma.Tensor.Dot_T.eq.Dot
open Tensor


@[main]
private lemma main
-- given
  (α β : Tensor ℝ [d])
  (q k : Tensor ℝ [d + d]) :
-- imply
  (α.rotaryMatrix @ q) @ (β.rotaryMatrix @ k) = q @ ((β - α).rotaryMatrix @ k) := by
-- proof
  apply Eq.trans (congrArg (fun t => t @ (β.rotaryMatrix @ k)) (Dot.eq.Dot_T q α.rotaryMatrix))
  apply Eq.trans (DotDot.eq.Dot_Dot.vmv q α.rotaryMatrixᵀ (β.rotaryMatrix @ k))
  apply congrArg (fun t => q @ t)
  apply Eq.trans (DotDot.eq.Dot_Dot.mmv α.rotaryMatrixᵀ β.rotaryMatrix k).symm
  apply congrArg (fun t => t @ k) (DotT.eq.RotaryMatrixSub α β)


-- created on 2026-09-03
-- updated on 2026-09-05
