import Lemma.Tensor.DotDot.eq.Dot_Dot
import Notation.Data.Tensor.Permute
import Lemma.Tensor.RotaryMatrix'.eq.DotDot_RotaryMatrix
import Lemma.Tensor.RotaryMatrixNeg.eq.TRotaryMatrix
import Lemma.Tensor.TDot.eq.DotTS
import Theorem.Data.Tensor.Functions
import Instance.Data.Vector.Basic.Dot
open Tensor
set_option maxHeartbeats 1000000


/-- Interleaved analogue of `Tensor.RotaryMatrixNeg.eq.TRotaryMatrix`. -/
@[path]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  (-θ).rotaryMatrix' = θ.rotaryMatrix'ᵀ := by
-- proof
  let P : Tensor ℝ [d + d, d + d] := interleave d
  let PT : Tensor ℝ [d + d, d + d] := Pᵀ
  have hθ : θ.rotaryMatrix' = (PT ⬝ᵥ θ.rotaryMatrix) ⬝ᵥ P :=
    (RotaryMatrix'.eq.DotDot_RotaryMatrix θ).trans rfl
  have hn : (-θ).rotaryMatrix' = (PT ⬝ᵥ (-θ).rotaryMatrix) ⬝ᵥ P :=
    (RotaryMatrix'.eq.DotDot_RotaryMatrix (-θ)).trans rfl
  rw [hn, RotaryMatrixNeg.eq.TRotaryMatrix θ, hθ]
  symm
  -- ⊢ ((PT ⬝ᵥ θ.rotaryMatrix) ⬝ᵥ P)ᵀ = (PT ⬝ᵥ θ.rotaryMatrixᵀ) ⬝ᵥ P
  apply Eq.trans (TDot.eq.DotTS (X := PT ⬝ᵥ θ.rotaryMatrix) (Y := P))
  -- ⊢ Pᵀ ⬝ᵥ (PT ⬝ᵥ θ.rotaryMatrix)ᵀ = (PT ⬝ᵥ θ.rotaryMatrixᵀ) ⬝ᵥ P
  change PT ⬝ᵥ (PT ⬝ᵥ θ.rotaryMatrix)ᵀ = (PT ⬝ᵥ θ.rotaryMatrixᵀ) ⬝ᵥ P
  apply Eq.trans (congrArg (fun t => PT ⬝ᵥ t) (TDot.eq.DotTS (X := PT) (Y := θ.rotaryMatrix)))
  -- ⊢ PT ⬝ᵥ (θ.rotaryMatrixᵀ ⬝ᵥ PTᵀ) = (PT ⬝ᵥ θ.rotaryMatrixᵀ) ⬝ᵥ P
  have hPTT : PTᵀ = P := EqTT P
  rw [hPTT]
  -- ⊢ PT ⬝ᵥ (θ.rotaryMatrixᵀ ⬝ᵥ P) = (PT ⬝ᵥ θ.rotaryMatrixᵀ) ⬝ᵥ P
  exact (DotDot.eq.Dot_Dot PT (θ.rotaryMatrixᵀ) P).symm


-- created on 2026-09-16
-- updated on 2026-10-26
