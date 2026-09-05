import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.DotT.eq.RotaryMatrixSub
import Lemma.Tensor.Dot_TInterleave.eq.Eye
import Lemma.Tensor.EqDotEye
import Lemma.Tensor.EqTT
import Lemma.Tensor.RotaryMatrix'.eq.DotDot_RotaryMatrix
import Lemma.Tensor.TDot.eq.DotTS
import sympy.functions.special.tensor_functions
import sympy.matrices.expressions.special
import sympy.tensor.functions
open Tensor
set_option maxHeartbeats 4000000


@[main]
private lemma main
-- given
  (α β : Tensor ℝ [d]) :
-- imply
  α.rotaryMatrix'ᵀ @ β.rotaryMatrix' = (β - α).rotaryMatrix' := by
-- proof
  let P : Tensor ℝ [d + d, d + d] := interleave d
  let PT : Tensor ℝ [d + d, d + d] := Pᵀ
  let αT : Tensor ℝ [d + d, d + d] := α.rotaryMatrixᵀ
  let AT : Tensor ℝ [d + d, d + d] := α.rotaryMatrix'ᵀ
  have hconj (θ : Tensor ℝ [d]) : θ.rotaryMatrix' = (PT @ θ.rotaryMatrix) @ P := by
    apply Eq.trans (RotaryMatrix'.eq.DotDot_RotaryMatrix θ)
    rfl
  let L : Tensor ℝ [d + d, d + d] := PT @ (αT @ P)
  let Mb : Tensor ℝ [d + d, d + d] := PT @ β.rotaryMatrix
  apply Eq.trans (b := AT @ β.rotaryMatrix') rfl
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => t @ β.rotaryMatrix')
    apply Eq.trans (b := id (α := Tensor ℝ [d + d, d + d]) ((PT @ α.rotaryMatrix) @ P)ᵀ)
    ·
      apply congrArg (fun t : Tensor ℝ [d + d, d + d] => id (α := Tensor ℝ [d + d, d + d]) tᵀ)
      apply hconj
    apply Eq.trans
    ·
      apply congrArg (id (α := Tensor ℝ [d + d, d + d]))
      apply TDot.eq.DotTS
    apply Eq.trans
    ·
      apply congrArg (fun t => id (α := Tensor ℝ [d + d, d + d]) (Pᵀ @ t))
      apply TDot.eq.DotTS
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => PT @ (αT @ t))
    apply EqTT
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => L @ t)
    apply hconj
  apply Eq.trans
  ·
    apply Eq.symm
    apply DotDot.eq.Dot_Dot
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => t @ P)
    apply DotDot.eq.Dot_Dot
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT @ t) @ P)
    apply DotDot.eq.Dot_Dot
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT @ (αT @ t)) @ P)
    apply Eq.symm
    apply DotDot.eq.Dot_Dot
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT @ (αT @ (t @ β.rotaryMatrix))) @ P)
    apply Dot_TInterleave.eq.Eye
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT @ (αT @ t)) @ P)
    apply EqDotEye
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT @ t) @ P)
    apply DotT.eq.RotaryMatrixSub
  apply Eq.symm
  apply hconj


-- created on 2026-09-05
-- updated on 2026-09-06
