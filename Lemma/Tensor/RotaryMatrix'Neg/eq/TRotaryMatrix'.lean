import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.TCast.as.T.of.Eq
import Notation.Data.Tensor.Permute
import Lemma.Tensor.RotaryMatrix'.eq.DotDot_RotaryMatrix
import Lemma.Tensor.RotaryMatrixNeg.eq.TRotaryMatrix
import Lemma.Tensor.TDot.eq.DotTS
import Theorem.Data.Tensor.Functions
import Instance.Data.Vector.Basic.Dot
open Bool Tensor
set_option maxHeartbeats 800000


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
  have hs : Tensor.matmul_shape [d + d, d + d] [d + d, d + d] = [d + d, d + d] := by
    simp [matmul_shape, broadcast_shape]
  let M : Tensor ℝ [d + d, d + d] :=
    cast (congrArg (Tensor ℝ) hs) (PT ⬝ᵥ θ.rotaryMatrix)
  have hθ : θ.rotaryMatrix' = (PT ⬝ᵥ θ.rotaryMatrix) ⬝ᵥ P :=
    (RotaryMatrix'.eq.DotDot_RotaryMatrix θ).trans rfl
  have hn : (-θ).rotaryMatrix' = (PT ⬝ᵥ (-θ).rotaryMatrix) ⬝ᵥ P :=
    (RotaryMatrix'.eq.DotDot_RotaryMatrix (-θ)).trans rfl
  rw [hn, RotaryMatrixNeg.eq.TRotaryMatrix θ, hθ]
  symm
  apply Eq.trans (TDot.eq.DotTS (X := PT ⬝ᵥ θ.rotaryMatrix) (Y := P))
  have hPT : Pᵀ = PT := rfl
  rw [hPT]
  have h2 : Mᵀ = θ.rotaryMatrixᵀ ⬝ᵥ P := by
    apply Eq.of.SEq
    apply (TCast.as.T.of.Eq hs (PT ⬝ᵥ θ.rotaryMatrix)).trans
    apply SEq.of.Eq
    apply Eq.trans (TDot.eq.DotTS (X := PT) (Y := θ.rotaryMatrix))
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => θ.rotaryMatrixᵀ ⬝ᵥ t)
    apply EqTT P
  apply Eq.trans
  ·
    apply congrArg (fun t : Tensor ℝ [d + d, d + d] => PT ⬝ᵥ t)
    apply Eq.of.SEq
    apply (TCast.as.T.of.Eq hs (PT ⬝ᵥ θ.rotaryMatrix)).symm
  ·
    rw [h2]
    apply (DotDot.eq.Dot_Dot PT (θ.rotaryMatrixᵀ) P).symm


-- created on 2026-09-16
-- updated on 2026-11-13
