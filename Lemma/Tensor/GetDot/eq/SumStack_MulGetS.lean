import torch.Tensor.unsqueeze
import torch.Tensor.permute
import Lemma.Tensor.Dot.eq.GetDotUnsqueeze_0
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.EqGetT
import Lemma.Tensor.Sum_0.eq.SumStack_Get
import Lemma.Tensor.SumStack.of.All_Eq
open Tensor
set_option maxHeartbeats 625000


@[path, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A @ B)[i, j] = ∑ k < l, id (α := Tensor α []) A[i][k] * id (α := Tensor α []) B[k][j] := by
-- proof
  rw [GetDot.eq.DotGetS]
  have := Dot.eq.SumMul__0 A[i] Bᵀ[j]
  conv_lhs => erw [this]
  rw [Sum_0.eq.SumStack_Get]
  apply SumStack.of.All_Eq
  intro k
  simp [GetElem.getElem]
  conv_lhs => erw [GetMul.eq.MulGetS.fin]
  have h := EqGetT.fin B k j
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
  erw [Vector.GetMap.eq.UFnGet.fin]
  simp [GetElem.getElem, HMul.hMul, id]
  congr


private lemma body
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [l])
  (B : Tensor α [l, n])
  (j : Fin n) :
-- imply
  (A @ B).get ⟨j, by simp [matmul_shape]; grind⟩ = ∑ k < l, id (α := Tensor α []) A[k] * id (α := Tensor α []) B[k][j] := by
-- proof
  have h := Dot.eq.GetDotUnsqueeze_0 A B
  have hg := congrArg (fun t => t.get ⟨j.val, by simp [matmul_shape]; grind⟩) h
  rw [hg]
  have h' := GetDot.eq.SumStack_MulGetS.fin (A.unsqueeze 0) B ⟨0, by simp⟩ j
  simp only [id] at h'
  erw [h']
  apply SumStack.of.All_Eq
  intro k
  erw [EqGetUnsqueeze_0.fin]
  congr


@[path, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [l])
  (B : Tensor α [l, n])
  (j : Fin n) :
-- imply
  (A @ B)[j]'(by simp [matmul_shape]; grind) = ∑ k < l, id (α := Tensor α []) A[k] * id (α := Tensor α []) B[k][j] := by
-- proof
  exact body A B j


-- created on 2026-08-14
-- updated on 2026-08-27
