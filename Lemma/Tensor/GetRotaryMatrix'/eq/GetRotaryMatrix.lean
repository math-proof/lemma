import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Fin.ToSplit.eq.Ite_Div_2
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.EqMul_0'0
import Lemma.Tensor.EqMul_1
import Lemma.Tensor.EqMul1
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetInterleave.eq.Delta_ToSplit
import Lemma.Tensor.GetTInterleave.eq.Delta_ToSplit
import Lemma.Tensor.RotaryMatrix'.eq.DotDot_RotaryMatrix
import Lemma.Tensor.SEqDotS.of.SEq
import sympy.functions.special.tensor_functions
import sympy.matrices.expressions.special
import sympy.tensor.functions
open Bool Nat Tensor Fin


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (i j : Fin (d + d)) :
-- imply
  θ.rotaryMatrix'[i][j] = θ.rotaryMatrix[i.toSplit][j.toSplit] := by
-- proof
  apply (congrArg (fun t : Tensor ℝ [d + d, d + d] => t[i][j]) (RotaryMatrix'.eq.DotDot_RotaryMatrix θ)).trans
  apply (GetDot.eq.Sum_MulGetS _ _ _ _).trans
  apply (Finset.sum_eq_single j.toSplit ?_ ?_).trans ?_
  ·
    intro k _ hk
    apply (congrArg (fun t : Tensor ℝ [] => ((interleave d)ᵀ @ θ.rotaryMatrix)[i][k] * t) (GetInterleave.eq.Delta_ToSplit k j)).trans
    simp [Delta.eq.Ite, Fin.val_injective.ne hk]
    apply Tensor.EqMul_0'0.nat
  ·
    intro h
    apply (h (Finset.mem_univ _)).elim
  ·
    apply (congrArg (fun t : Tensor ℝ [] => ((interleave d)ᵀ @ θ.rotaryMatrix)[i][j.toSplit] * t) (GetInterleave.eq.Delta_ToSplit j.toSplit j)).trans
    simp [Delta.eq.Ite]
    apply (Tensor.EqMul_1.nat _).trans
    apply (congrArg (fun t : Tensor ℝ [d + d, d + d] => t[i][j.toSplit]) (Eq.of.SEq (SEqDotS.of.SEq (SEqCast.of.Eq (by simp) (interleave d)ᵀ) θ.rotaryMatrix)).symm).trans
    apply (GetDot.eq.Sum_MulGetS _ _ _ _).trans
    apply (Finset.sum_eq_single i.toSplit ?_ ?_).trans ?_
    ·
      intro k _ hk
      apply (congrArg (fun t : Tensor ℝ [] => t * id (α := Tensor ℝ []) θ.rotaryMatrix[k][j.toSplit]) (GetTInterleave.eq.Delta_ToSplit i k)).trans
      simp [Delta.eq.Ite, Fin.val_injective.ne hk]
      apply Tensor.EqMul0_0.nat
    ·
      intro h
      apply (h (Finset.mem_univ _)).elim
    ·
      apply (congrArg (fun t : Tensor ℝ [] => t * id (α := Tensor ℝ []) θ.rotaryMatrix[i.toSplit][j.toSplit]) (GetTInterleave.eq.Delta_ToSplit i i.toSplit)).trans
      simp [Delta.eq.Ite]
      apply Tensor.EqMul1.nat


-- created on 2026-09-05
