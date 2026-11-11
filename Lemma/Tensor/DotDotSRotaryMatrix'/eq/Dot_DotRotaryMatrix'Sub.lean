import Notation.Data.Tensor.Permute
import Lemma.Tensor.DotT.eq.RotaryMatrix'Sub
import Lemma.Tensor.Dot_T.eq.Dot
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path]
private lemma main
-- given
  (α β : Tensor ℝ [d])
  (q k : Tensor ℝ [d + d]) :
-- imply
  (α.rotaryMatrix' ⬝ᵥ q) ⬝ᵥ (β.rotaryMatrix' ⬝ᵥ k) = q ⬝ᵥ ((β - α).rotaryMatrix' ⬝ᵥ k) := by
-- proof
  apply Eq.trans (congrArg (fun t => t ⬝ᵥ (β.rotaryMatrix' ⬝ᵥ k)) (Dot.eq.Dot_T q α.rotaryMatrix'))
  apply Eq.trans (DotDot.eq.Dot_Dot.vmv q α.rotaryMatrix'ᵀ (β.rotaryMatrix' ⬝ᵥ k))
  apply congrArg (fun t => q ⬝ᵥ t)
  apply Eq.trans (DotDot.eq.Dot_Dot.mmv α.rotaryMatrix'ᵀ β.rotaryMatrix' k).symm
  apply congrArg (fun t => t ⬝ᵥ k) (DotT.eq.RotaryMatrix'Sub α β)


-- created on 2026-09-16
-- updated on 2026-10-26
