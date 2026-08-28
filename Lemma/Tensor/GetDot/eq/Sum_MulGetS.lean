import Lemma.Fin.Sum.of.All_Eq
import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.Dot.eq.GetDotUnsqueeze_0
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Vector.GetMap.eq.UFnGet
open Fin Tensor Vector
set_option maxHeartbeats 400000


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetDot.eq.Sum_MulGetS |
| fin | Tensor.GetDot.eq.Sum_MulGetS.fin |
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
  conv_lhs => erw [@Tensor.GetMul.eq.MulGetS.fin]
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
  erw [GetMap.eq.UFnGet.fin]
  rfl


@[main, fin]
private lemma une
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [l])
  (B : Tensor α [l, n])
  (j : Fin n) :
-- imply
  (A @ B)[j]'(by simp [matmul_shape]; grind) = ∑ k : Fin l, id (α := Tensor α []) A[k] * id (α := Tensor α []) B[k][j] := by
-- proof
  have h := Dot.eq.GetDotUnsqueeze_0 A B
  simp [GetElem.getElem]
  apply (Get.of.Eq.fin h ⟨j, by grind⟩).trans
  have h' := main (A.unsqueeze 0) B ⟨0, by simp⟩ j
  simp [GetElem.getElem] at h' ⊢
  conv_lhs => erw [h']
  apply Sum.of.All_Eq
  intro k
  erw [EqGetUnsqueeze_0.fin]


@[main, fin]
private lemma mv
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l])
  (i : Fin m) :
-- imply
  (A @ B)[i]'(by grind [matmul_shape]) = ∑ k : Fin l, id (α := Tensor α []) A[i][k] * id (α := Tensor α []) B[k] := by
-- proof
  simp [GetElem.getElem]
  have h := GetDot.eq.DotGet.une.fin A B i
  simp at h
  erw [h]
  have hsum := Dot.eq.SumMul__0 (A.get i) B
  erw [hsum]
  rw [Sum_0.eq.Sum_Get]
  apply Sum.of.All_Eq
  intro k
  simp [id, GetElem.getElem]
  conv_lhs => erw [@Tensor.GetMul.eq.MulGetS.fin]
  simp [HMul.hMul]
  apply Eq.of.EqDataS
  simp
  ext t
  fin_cases t
  simp
  erw [DataMul.eq.MulDataS]
  rw [Vector.Head.eq.Get_0.fin]
  erw [Vector.GetMul.eq.MulGetS.fin]
  congr 1
  erw [GetMap.eq.UFnGet.fin]
  congr 1


-- created on 2026-07-31
-- updated on 2026-08-27
