import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetHstack.eq.Get.of.Lt
import Lemma.Tensor.GetHstack.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetTranspose.eq.Get
import sympy.tensor.Basic
open Tensor
set_option maxHeartbeats 4000000


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.TAppendHstackS.eq.AppendHstackSTS |
| comm | Tensor.AppendHstackSTS.eq.TAppendHstackS |
-/
@[main, comm]
private lemma main
-- given
  (A : Tensor α [n, p])
  (B : Tensor α [n, q])
  (C : Tensor α [m, p])
  (D : Tensor α [m, q]) :
-- imply
  (A.hstack B ++ C.hstack D)ᵀ =
    Aᵀ.hstack Cᵀ ++ Bᵀ.hstack Dᵀ := by
-- proof
  let M : Tensor α [n + m, p + q] := A.hstack B ++ C.hstack D
  change Mᵀ = Aᵀ.hstack Cᵀ ++ Bᵀ.hstack Dᵀ
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  have hi_pq : (i : ℕ) < p + q := i.isLt
  have hj_nm : (j : ℕ) < n + m := j.isLt
  conv_lhs =>
    erw [GetTranspose.eq.Get.fin]
  if hi : (i : ℕ) < p then
    if hj : (j : ℕ) < n then
      have hrow := GetAppend.eq.Get.of.Lt (A := A.hstack B) (B := C.hstack D) hj
      have hcell := GetHstack.eq.Get.of.Lt (A := A) (B := B) (i := ⟨j, hj⟩) hi
      have hT := GetTranspose.eq.Get.fin A (i := ⟨j, hj⟩) (j := ⟨i, hi⟩)
      have hRrow := GetAppend.eq.Get.of.Lt (A := Aᵀ.hstack Cᵀ) (B := Bᵀ.hstack Dᵀ) hi
      have hRcell := GetHstack.eq.Get.of.Lt (A := Aᵀ) (B := Cᵀ) (i := ⟨i, hi⟩) hj
      simp only [id] at hcell hRcell
      refine (congrArg (fun t : Tensor α [p + q] => t[i]) hrow).trans ?_
      refine hcell.trans (hT.symm.trans ?_)
      refine hRcell.symm.trans ?_
      exact congrArg (fun t : Tensor α [n + m] => t[j]) hRrow.symm
    else
      have hjn : (j : ℕ) - n < m := Nat.sub_lt_left_of_lt_add (le_of_not_gt hj) hj_nm
      have hrow := GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := A.hstack B) (B := C.hstack D) (le_of_not_gt hj) hj_nm
      have hcell := GetHstack.eq.Get.of.Lt (A := C) (B := D) (i := ⟨(j : ℕ) - n, hjn⟩) hi
      have hT := GetTranspose.eq.Get.fin C (i := ⟨(j : ℕ) - n, hjn⟩) (j := ⟨i, hi⟩)
      have hRrow := GetAppend.eq.Get.of.Lt (A := Aᵀ.hstack Cᵀ) (B := Bᵀ.hstack Dᵀ) hi
      have hRcell := GetHstack.eq.Get_Sub.of.GtAdd.Ge (A := Aᵀ) (B := Cᵀ) (i := ⟨i, hi⟩) (le_of_not_gt hj) hj_nm
      simp only [id] at hcell hRcell
      refine (congrArg (fun t : Tensor α [p + q] => t[i]) hrow).trans ?_
      refine hcell.trans (hT.symm.trans ?_)
      refine hRcell.symm.trans ?_
      exact congrArg (fun t : Tensor α [n + m] => t[j]) hRrow.symm
  else
    have hip : (i : ℕ) - p < q := Nat.sub_lt_left_of_lt_add (le_of_not_gt hi) hi_pq
    if hj : (j : ℕ) < n then
      have hrow := GetAppend.eq.Get.of.Lt (A := A.hstack B) (B := C.hstack D) hj
      have hcell := GetHstack.eq.Get_Sub.of.GtAdd.Ge (A := A) (B := B) (i := ⟨j, hj⟩) (le_of_not_gt hi) hi_pq
      have hT := GetTranspose.eq.Get.fin B (i := ⟨j, hj⟩) (j := ⟨(i : ℕ) - p, hip⟩)
      have hRrow := GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := Aᵀ.hstack Cᵀ) (B := Bᵀ.hstack Dᵀ) (le_of_not_gt hi) hi_pq
      have hRcell := GetHstack.eq.Get.of.Lt (A := Bᵀ) (B := Dᵀ) (i := ⟨(i : ℕ) - p, hip⟩) hj
      simp only [id] at hcell hRcell
      refine (congrArg (fun t : Tensor α [p + q] => t[i]) hrow).trans ?_
      refine hcell.trans (hT.symm.trans ?_)
      refine hRcell.symm.trans ?_
      exact congrArg (fun t : Tensor α [n + m] => t[j]) hRrow.symm
    else
      have hjn : (j : ℕ) - n < m := Nat.sub_lt_left_of_lt_add (le_of_not_gt hj) hj_nm
      have hrow := GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := A.hstack B) (B := C.hstack D) (le_of_not_gt hj) hj_nm
      have hcell := GetHstack.eq.Get_Sub.of.GtAdd.Ge (A := C) (B := D) (i := ⟨(j : ℕ) - n, hjn⟩) (le_of_not_gt hi) hi_pq
      have hT := GetTranspose.eq.Get.fin D (i := ⟨(j : ℕ) - n, hjn⟩) (j := ⟨(i : ℕ) - p, hip⟩)
      have hRrow := GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := Aᵀ.hstack Cᵀ) (B := Bᵀ.hstack Dᵀ) (le_of_not_gt hi) hi_pq
      have hRcell := GetHstack.eq.Get_Sub.of.GtAdd.Ge (A := Bᵀ) (B := Dᵀ) (i := ⟨(i : ℕ) - p, hip⟩) (le_of_not_gt hj) hj_nm
      simp only [id] at hcell hRcell
      refine (congrArg (fun t : Tensor α [p + q] => t[i]) hrow).trans ?_
      refine hcell.trans (hT.symm.trans ?_)
      refine hRcell.symm.trans ?_
      exact congrArg (fun t : Tensor α [n + m] => t[j]) hRrow.symm


-- created on 2026-09-02
