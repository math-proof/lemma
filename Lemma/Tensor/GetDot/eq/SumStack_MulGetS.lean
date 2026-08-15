import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Dot.eq.GetDotUnsqueeze_0
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.Sum_0.eq.SumStack_Get
import Lemma.Tensor.SumStack.of.All_Eq
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.Head.eq.Get_0
open Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A @ B)[i, j] = ∑ k < l, (let a : Tensor α [] := A[i][k]; a) * (let b : Tensor α [] := B[k][j]; b) := by
-- proof
  rw [GetDot.eq.DotGetS]
  have := Dot.eq.SumMul__0 A[i] Bᵀ[j]
  conv_lhs => erw [this]
  rw [Sum_0.eq.SumStack_Get]
  apply SumStack.of.All_Eq
  intro k
  simp [GetElem.getElem]
  conv_lhs => erw [GetMul.eq.MulGetS.fin]
  have h := GetTranspose.eq.Get.fin B k j
  have := congrArg (fun x => (A.get i).get k * x) h
  simp [HMul.hMul] at ⊢ this
  erw [this]
  apply Eq.of.EqDataS
  simp
  ext t
  fin_cases t
  simp
  erw [DataMul.eq.MulDataS]
  rw [Vector.Head.eq.Get_0.fin]
  erw [Vector.GetMul.eq.MulGetS.fin]
  congr 1
  simp


@[main, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [l])
  (B : Tensor α [l, n])
  (j : Fin n) :
-- imply
  (A @ B)[j]'(by simp [matmul_shape]; grind) = ∑ k < l, (let a : Tensor α [] := A[k]; a) * (let b : Tensor α [] := B[k][j]; b) := by
-- proof
  have h := Dot.eq.GetDotUnsqueeze_0 A B
  simp [GetElem.getElem]
  conv_lhs => erw [h]
  have h' := GetDot.eq.SumStack_MulGetS.fin (A.unsqueeze 0) B ⟨0, by simp⟩ j
  conv_lhs => erw [h']
  apply SumStack.of.All_Eq
  intro k
  simp
  erw [EqGetUnsqueeze_0.fin]


-- created on 2026-08-14
