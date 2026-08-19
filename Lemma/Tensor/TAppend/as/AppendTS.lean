import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.EqSwap_0'1
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
open Bool List Tensor
set_option maxHeartbeats 400000


@[main]
private lemma main
-- given
  (A : Tensor α [n, d])
  (B : Tensor α [m, d]) :
-- imply
  let AT : Tensor α ([d] ++ n :: []) := cast (congrArg (Tensor α) (EqSwap_0'1 n d)) Aᵀ
  let BT : Tensor α ([d] ++ m :: []) := cast (congrArg (Tensor α) (EqSwap_0'1 m d)) Bᵀ
  (A ++ B)ᵀ ≃ AT ++ BT := by
-- proof
  extract_lets AT BT
  apply (SEq_Cast.of.Eq (EqSwap_0'1 (n + m) d) (A ++ B)ᵀ).trans
  apply SEq.of.Eq
  apply Eq.of.All_EqGetS
  intro i
  apply Eq.of.All_EqGetS
  intro j
  apply Eq.of.SEq
  have hL :=
    GetCast.as.Get.of.Eq.GtLength_0.right.fin
      (s' := [d, n + m])
      (by simp)
      (EqSwap_0'1 (n + m) d)
      (A ++ B)ᵀ
      i
  have hLj :=
    SEqGetS.of.SEq.GtLength (i := (j : ℕ))
      (h₀ := by simp [Tensor.length])
      hL
  have hT := GetTranspose.eq.Get.fin (A ++ B) (i := j) (j := i)
  refine hLj.trans ((SEq.of.Eq hT).trans ?_)
  if hj : (j : ℕ) < n then
    have hAj := GetAppend.eq.Get.of.Lt (A := A) (B := B) hj
    have hATj :=
      GetCast.as.Get.of.Eq.GtLength_0.right.fin
        (s' := [d, n])
        (by simp)
        (EqSwap_0'1 n d)
        Aᵀ
        i
    have hATjj :=
      SEqGetS.of.SEq.GtLength (i := (j : ℕ))
        (h₀ := by
          simp [Tensor.length]
          exact hj)
        hATj
    have hTA := GetTranspose.eq.Get.fin A (i := ⟨j, hj⟩) (j := i)
    refine (SEq.of.Eq (congrArg (fun t => t[i.val]) hAj)).trans ?_
    refine (SEq.of.Eq hTA.symm).trans ?_
    refine hATjj.symm.trans ?_
    have hget := GetAppend.eq.Get.of.Lt.batch hj AT BT i
    exact SEq.of.Eq hget.symm
  else
    have hBj := GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := A) (B := B) (by omega) j.isLt
    have hBTj :=
      GetCast.as.Get.of.Eq.GtLength_0.right.fin
        (s' := [d, m])
        (by simp)
        (EqSwap_0'1 m d)
        Bᵀ
        i
    have hBTjj :=
      SEqGetS.of.SEq.GtLength (i := (j : ℕ) - n)
        (h₀ := by
          simp [Tensor.length]
          omega)
        hBTj
    have hTB := GetTranspose.eq.Get.fin B (i := ⟨(j : ℕ) - n, by omega⟩) (j := i)
    refine (SEq.of.Eq (congrArg (fun t => t[i.val]) hBj)).trans ?_
    refine (SEq.of.Eq hTB.symm).trans ?_
    refine hBTjj.symm.trans ?_
    have hget :=
      GetAppend.eq.Get_Sub.of.GtAdd.Ge.batch (by omega) j.isLt AT BT i
    extract_lets h_j at hget
    exact SEq.of.Eq hget.symm


-- created on 2026-08-19
