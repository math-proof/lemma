import Lemma.Fin.Sum.of.All_Eq
import Lemma.Tensor.Dot.eq.GetDotUnsqueeze_0
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Bool.SEq.is.Eq
import Lemma.Vector.Head.eq.Get_0
open Fin Tensor Bool


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetDot.eq.Sum_MulGetS |
| fin | Tensor.GetDot.eq.Sum_MulGetS.fin |
| une | Tensor.GetDot.eq.Sum_MulGetS.une |
| une.fin | Tensor.GetDot.eq.Sum_MulGetS.une.fin |
-/
@[main, fin]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (A @ B)[i, j] = ∑ k : Fin l, id (α := Tensor α []) A[i][k] * id (α := Tensor α []) B[k][j] := by
-- proof
  rw [GetDot.eq.DotGetS]
  have := Dot.eq.SumMul__0 A[i] Bᵀ[j]
  conv_lhs => erw [this]
  rw [Sum_0.eq.Sum_Get]
  congr
  funext k
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
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [l])
  (B : Tensor α [l, n])
  (j : Fin n) :
-- imply
  (A @ B)[j]'(by grind [matmul_shape]) = ∑ k : Fin l, id (α := Tensor α []) A[k] * id (α := Tensor α []) B[k][j] := by
-- proof
  have h := Dot.eq.GetDotUnsqueeze_0 A B
  simp [GetElem.getElem]
  conv_lhs => erw [h]
  have h' := GetDot.eq.Sum_MulGetS.fin (A.unsqueeze 0) B ⟨0, by simp⟩ j
  conv_lhs => erw [h']
  apply Sum.of.All_Eq
  intro k
  simp
  erw [EqGetUnsqueeze_0.fin]


-- created on 2026-07-31
-- updated on 2026-08-19
