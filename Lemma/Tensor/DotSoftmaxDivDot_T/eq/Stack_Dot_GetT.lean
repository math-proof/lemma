import Lemma.List.EqSwap_0'1
import Lemma.Tensor.Dot.eq.Stack_DotGetS
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.GetDot.as.DotGet
import Lemma.Tensor.GetSoftmax.eq.SoftmaxGet.of.GtGet_0.LtAdd_1Length
import Lemma.Tensor.SEqDotS.of.SEq
import Lemma.Tensor.SEqSoftmaxS.of.SEq
open List Tensor


@[main]
private lemma main
-- given
  (Q K V : Tensor ℝ [n, d_z]) :
-- imply
  ((Q @ Kᵀ) / √d_z).softmax @ V = [i < n] [j < d_z] ((Q[i] @ Kᵀ) / √d_z).softmax @ Vᵀ[j] := by
-- proof
  have hQK : matmul_shape [n, d_z] [d_z, n] = [n, n] := by simp [matmul_shape, broadcast_shape]
  let KT : Tensor ℝ [d_z, n] := cast (congrArg (Tensor ℝ) (EqSwap_0'1 n d_z)) Kᵀ
  let QK : Tensor ℝ [n, n] := cast (congrArg (Tensor ℝ) hQK) (Q @ KT)
  let A : Tensor ℝ [n, n] := QK / √d_z
  apply Bool.Eq.of.SEq
  apply SEq.trans (b := A.softmax @ V)
  ·
    apply SEq.symm
    apply SEqDotS.of.SEq
    apply SEqSoftmaxS.of.SEq
    apply Bool.SEqUFnS.of.SEq _ (fun {s} (X : Tensor ℝ s) => X / √d_z)
    apply SEq.trans (b := Q @ KT)
    ·
      apply Bool.SEqCast.of.Eq hQK
    ·
      apply SEqDotS.of.SEq.left
      apply Bool.SEqCast.of.Eq (EqSwap_0'1 n d_z)
  ·
    apply Bool.SEq.of.Eq
    rw [Dot.eq.Stack_DotGetS]
    apply Eq.of.All_EqGetS.fin
    intro i
    apply Eq.of.All_EqGetS.fin
    intro j
    conv_lhs =>
      erw [EqGetStack.fin (i := i)]
      erw [EqGetStack.fin (i := j)]
    conv_rhs =>
      erw [EqGetStack.fin (i := i)]
      erw [EqGetStack.fin (i := j)]
    apply Bool.Eq.of.SEq
    apply SEqDotS.of.SEq
    apply SEq.trans
    ·
      apply Bool.SEq.of.Eq
      have hget : (A.softmax 1)[i] = A[i].softmax 0 :=
        GetSoftmax.eq.SoftmaxGet.of.GtGet_0.LtAdd_1Length (s := [n, n]) (d := 0) (by grind) i.isLt A
      simpa [Tensor.softmax] using hget
    ·
      apply SEqSoftmaxS.of.SEq _ 0
      simp [GetElem.getElem]
      show (A.get i : Tensor ℝ [n]) ≃ ((Q.get i : Tensor ℝ [d_z]) @ Kᵀ) / √d_z
      apply SEq.trans (b := QK.get i / √↑d_z)
      ·
        apply Bool.SEq.of.Eq
        simpa [A] using GetDiv.eq.DivGet.scalar.fin (X := QK) (a := √d_z) (i := i)
      ·
        apply Bool.SEqUFnS.of.SEq _ (fun {s} (X : Tensor ℝ s) => X / √d_z)
        apply SEq.trans (b := (Q.get i : Tensor ℝ [d_z]) @ KT)
        ·
          apply (GetCast.as.Get.of.Eq.GtLength_0.right.fin (by grind) hQK (Q @ KT) i).trans
          convert GetDot.as.DotGet.fin (s := []) (k := d_z) (n' := d_z) (k' := n) Q KT i
        ·
          apply SEqDotS.of.SEq.left
          apply Bool.SEqCast.of.Eq (EqSwap_0'1 n d_z)


-- created on 2023-05-22
