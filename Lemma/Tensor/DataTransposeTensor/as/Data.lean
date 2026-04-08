import Lemma.Tensor.EqGetS.of.Data.as.FlattenTransposeSplitAt_1
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteTail.eq.CastRotate.of.LeLength
import Lemma.Tensor.Permute__0.eq.Cast
import sympy.tensor.tensor
open List Tensor Vector


@[main]
private lemma main
-- given
  (v : List.Vector α n) :
-- imply
  (⟨cast (congrArg (List.Vector α) (by simp)) v⟩ : Tensor α [n, 1])ᵀ.data ≃ v := by
-- proof
  apply SEq.of.All_EqGetS.Eq.fin
  .
    intro t
    have h_t := t.isLt
    conv_rhs at h_t =>
      simp
    simp [EqSwap_0'1] at h_t
    unfold Tensor.T
    unfold Tensor.transpose
    simp
    rw [Permute__0.eq.Cast]
    sorry
  .
    simp [EqSwap_0'1]


-- created on 2026-04-07
