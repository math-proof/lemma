import Lemma.Tensor.DotDot.eq.Dot_Dot
import Notation.Data.Tensor.Permute
import Lemma.Tensor.DotT.eq.RotaryMatrixSub
import Lemma.Tensor.Dot_TInterleave.eq.Eye
import Lemma.Tensor.EqDotEye
import Lemma.Tensor.TDot.eq.DotTS
import Def.Data.Tensor.Eye
import Theorem.Data.Tensor.Functions
import Instance.Data.Vector.Basic.Dot
open Tensor
set_option maxHeartbeats 800000


@[path]
private lemma main
-- given
  (α β : Tensor ℝ [d]) :
-- imply
  α.rotaryMatrix'ᵀ ⬝ᵥ β.rotaryMatrix' = (β - α).rotaryMatrix' := by
-- proof
  let P : Tensor ℝ [d + d, d + d] := interleave d
  let PT : Tensor ℝ [d + d, d + d] := Pᵀ
  let αT : Tensor ℝ [d + d, d + d] := α.rotaryMatrixᵀ
  let AT : Tensor ℝ [d + d, d + d] := α.rotaryMatrix'ᵀ
  have hconj (θ : Tensor ℝ [d]) : θ.rotaryMatrix' = (PT ⬝ᵥ θ.rotaryMatrix) ⬝ᵥ P := by
    apply Eq.trans (RotaryMatrix'.eq.DotDot_RotaryMatrix θ)
    rfl
  let L : Tensor ℝ [d + d, d + d] := PT ⬝ᵥ (αT ⬝ᵥ P)
  let Mb : Tensor ℝ [d + d, d + d] := PT ⬝ᵥ β.rotaryMatrix
  apply Eq.trans (b := AT ⬝ᵥ β.rotaryMatrix') rfl
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => t ⬝ᵥ β.rotaryMatrix')
    apply Eq.trans (b := id (α := Tensor ℝ [d + d, d + d]) ((PT ⬝ᵥ α.rotaryMatrix) ⬝ᵥ P)ᵀ)
    ·
      apply congrArg (fun t : Tensor ℝ [d + d, d + d] => id (α := Tensor ℝ [d + d, d + d]) tᵀ)
      apply hconj
    apply Eq.trans
    ·
      apply congrArg (id (α := Tensor ℝ [d + d, d + d]))
      apply TDot.eq.DotTS
    apply Eq.trans
    ·
      apply congrArg (fun t : Tensor ℝ [d + d, d + d] => id (α := Tensor ℝ [d + d, d + d]) (Pᵀ ⬝ᵥ t))
      apply TDot.eq.DotTS
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => PT ⬝ᵥ (αT ⬝ᵥ t))
    apply EqTT
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => L ⬝ᵥ t)
    apply hconj
  apply Eq.trans
  ·
    apply Eq.symm
    apply DotDot.eq.Dot_Dot
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => t ⬝ᵥ P)
    apply DotDot.eq.Dot_Dot
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT ⬝ᵥ t) ⬝ᵥ P)
    apply DotDot.eq.Dot_Dot
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT ⬝ᵥ (αT ⬝ᵥ t)) ⬝ᵥ P)
    apply Eq.symm
    apply DotDot.eq.Dot_Dot
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT ⬝ᵥ (αT ⬝ᵥ (t ⬝ᵥ β.rotaryMatrix))) ⬝ᵥ P)
    apply Dot_TInterleave.eq.Eye
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT ⬝ᵥ (αT ⬝ᵥ t)) ⬝ᵥ P)
    apply EqDotEye
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => (PT ⬝ᵥ t) ⬝ᵥ P)
    apply DotT.eq.RotaryMatrixSub
  apply Eq.symm
  apply hconj


-- created on 2026-09-05
-- updated on 2026-11-13
