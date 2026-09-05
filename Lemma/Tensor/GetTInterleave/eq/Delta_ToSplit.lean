import Lemma.Bool.SEq.is.Eq
import Lemma.Fin.ToSplit.eq.Ite_Div_2
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetInterleave.eq.Delta_ToSplit
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.Interleave.eq.AppendStackS_Delta
import sympy.functions.special.tensor_functions
open Bool Tensor Fin


@[main]
private lemma main
-- given
  (i k : Fin (d + d)) :
-- imply
  (cast (congrArg (Tensor ℝ) (a₂ := [d + d, d + d]) (by simp)) (interleave d)ᵀ)[i][k] =
    (↑(KroneckerDelta (k : ℕ) (toSplit i : ℕ)) : Tensor ℝ []) := by
-- proof
  apply (Eq.of.SEq (SEqGetS.of.SEq.GtLength (by simp [Tensor.length]) (GetCast.as.Get.of.Eq.GtLength_0.right.fin (s' := [d + d, d + d]) (by simp) (by simp) _ i))).trans
  apply (GetTranspose.eq.Get.fin (interleave d) k i).trans
  apply GetInterleave.eq.Delta_ToSplit


-- created on 2026-09-05
