import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Bool.SEq.is.Eq
import Lemma.Vector.Head.eq.Get_0
open Tensor Bool


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
  (A @ B)[i, j] = ∑ k : Fin l, (let a : Tensor α [] := A[i][k]; a) * (let b : Tensor α [] := B[k][j]; b) := by
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


-- created on 2026-07-31
