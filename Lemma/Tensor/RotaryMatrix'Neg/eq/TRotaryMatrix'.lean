import Lemma.Tensor.DotDot.eq.Dot_Dot
import torch.Tensor.permute
import Lemma.Tensor.EqTT
import Lemma.Tensor.RotaryMatrix'.eq.DotDot_RotaryMatrix
import Lemma.Tensor.RotaryMatrixNeg.eq.TRotaryMatrix
import Lemma.Tensor.TDot.eq.DotTS
import sympy.functions.special.tensor_functions
import sympy.matrices.expressions.special
import torch.functions
open Tensor
set_option maxHeartbeats 8000000


/-- Interleaved analogue of `Tensor.RotaryMatrixNeg.eq.TRotaryMatrix`. -/
@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  (-θ).rotaryMatrix' = θ.rotaryMatrix'ᵀ := by
-- proof
  let P : Tensor ℝ [d + d, d + d] := interleave d
  let PT : Tensor ℝ [d + d, d + d] := Pᵀ
  have hθ : θ.rotaryMatrix' = (PT @ θ.rotaryMatrix) @ P :=
    (RotaryMatrix'.eq.DotDot_RotaryMatrix θ).trans rfl
  have hn : (-θ).rotaryMatrix' = (PT @ (-θ).rotaryMatrix) @ P :=
    (RotaryMatrix'.eq.DotDot_RotaryMatrix (-θ)).trans rfl
  rw [hn, RotaryMatrixNeg.eq.TRotaryMatrix θ, hθ]
  symm
  -- ⊢ ((PT @ θ.rotaryMatrix) @ P)ᵀ = (PT @ θ.rotaryMatrixᵀ) @ P
  apply Eq.trans (TDot.eq.DotTS (X := PT @ θ.rotaryMatrix) (Y := P))
  -- ⊢ Pᵀ @ (PT @ θ.rotaryMatrix)ᵀ = (PT @ θ.rotaryMatrixᵀ) @ P
  change PT @ (PT @ θ.rotaryMatrix)ᵀ = (PT @ θ.rotaryMatrixᵀ) @ P
  apply Eq.trans (congrArg (fun t => PT @ t) (TDot.eq.DotTS (X := PT) (Y := θ.rotaryMatrix)))
  -- ⊢ PT @ (θ.rotaryMatrixᵀ @ PTᵀ) = (PT @ θ.rotaryMatrixᵀ) @ P
  have hPTT : PTᵀ = P := EqTT P
  rw [hPTT]
  -- ⊢ PT @ (θ.rotaryMatrixᵀ @ P) = (PT @ θ.rotaryMatrixᵀ) @ P
  exact (DotDot.eq.Dot_Dot PT (θ.rotaryMatrixᵀ) P).symm


-- created on 2026-09-16
-- updated on 2026-09-16
