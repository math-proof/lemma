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
  ((rotaryMatrix α) @ q) @ ((rotaryMatrix β) @ k) = q @ ((rotaryMatrix (β - α)) @ k) := by
-- proof
  apply Eq.trans (congrArg (fun t => t @ ((rotaryMatrix β) @ k)) (Dot.eq.Dot_T q (rotaryMatrix α)))
  apply Eq.trans (DotDot.eq.Dot_Dot.vmv q (rotaryMatrix α)ᵀ ((rotaryMatrix β) @ k))
  apply congrArg (fun t => q @ t)
  apply Eq.trans (DotDot.eq.Dot_Dot.mmv (rotaryMatrix α)ᵀ (rotaryMatrix β) k).symm
  apply congrArg (fun t => t @ k) (DotT.eq.RotaryMatrixSub α β)


-- created on 2026-09-03
