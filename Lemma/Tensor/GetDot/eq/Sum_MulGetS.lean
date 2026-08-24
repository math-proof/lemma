import Lemma.Fin.Sum.of.All_Eq
import Lemma.Tensor.Dot.eq.GetDotUnsqueeze_0
import Lemma.Tensor.Dot.eq.SelectDot_Unsqueeze_1
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt.GtGet_0.GtLength_0
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.SelectCast.as.Select.of.Eq
import Lemma.Tensor.Sum_0.eq.Sum_Get
import Lemma.Tensor.SEqMulS.of.SEq.SEq
import Lemma.Tensor.DataMul.eq.MulData
open Fin Tensor
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
  have h := Dot.eq.SelectDot_Unsqueeze_1 A B
  have hshape : matmul_shape [m, l] ([l].insertIdx 1 1) = [m, 1] := by
    simp [matmul_shape, broadcast_shape]
  let AB : Tensor α [m, 1] := cast (congrArg (Tensor α) hshape) (A @ (B.unsqueeze 1))
  have hsc := SelectCast.as.Select.of.Eq
    (s := matmul_shape [m, l] ([l].insertIdx 1 1))
    (s' := [m, 1])
    hshape (A @ (B.unsqueeze 1))
    ⟨1, by simp [matmul_shape, broadcast_shape]⟩
    ⟨0, by simp [matmul_shape, broadcast_shape]⟩
  have hsel := GetSelect_1.as.Get.of.Lt.GtGet_0.GtLength_0
    (s := [1]) (n := m) (i := 0) (j := (i : ℕ))
    (by simp) (by simp) i.isLt AB
  have hrow := GetCast.as.Get.of.Eq.GtLength_0.right.fin
    (s' := [m, 1]) (by simp) hshape (A @ (B.unsqueeze 1)) ⟨i, by simp⟩
  have hcell := SEqGetS.of.SEq.GtLength (i := 0) (by simp [Tensor.length]) hrow
  have h' := main A (B.unsqueeze 1) i ⟨0, by simp⟩
  have hlen : ((A @ (B.unsqueeze 1)).select ⟨1, by simp [matmul_shape]⟩
      ⟨0, by simp [matmul_shape, broadcast_shape]⟩).length > (i : ℕ) := by
    have hlen_sc := Length.of.SEq hsc
    have hlen_AB : (AB.select ⟨1, by simp⟩ ⟨0, by simp⟩).length = m :=
      EqLength _
    exact lt_of_lt_of_eq i.isLt (hlen_AB.symm.trans hlen_sc)
  have hget := SEqGetS.of.SEq.GtLength (i := (i : ℕ)) hlen hsc.symm
  simp [GetElem.getElem]
  conv_lhs => erw [h]
  apply Bool.Eq.of.SEq
  apply hget.trans
  apply hsel.trans
  apply hcell.trans
  apply Bool.SEq.of.Eq
  refine Eq.trans ?_ (h'.trans ?_)
  ·
    simp [GetElem.getElem]
    rfl
  ·
    apply Sum.of.All_Eq
    intro k
    simp [id, GetElem.getElem]
    apply Eq.of.EqDataS
    simp [DataMul.eq.MulData.head]
    congr 1
    congr 1
    apply Bool.Eq.of.SEq
    apply SEqDataS.of.SEq.Eq (by rfl)
    have hrow := GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0 (s := [l]) (d := 1) (i := (k : ℕ)) (by simp) (by simp) k.isLt B
    have hcell := SEqGetS.of.SEq.GtLength (i := 0) (by grind) hrow
    apply hcell.trans
    apply Bool.SEq.of.Eq
    apply EqGetUnsqueeze_0.fin


-- created on 2026-07-31
-- updated on 2026-08-24
