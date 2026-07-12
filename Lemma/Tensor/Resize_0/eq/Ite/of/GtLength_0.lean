import Lemma.Tensor.SEqRepeat.of.Eq_1
import Lemma.Nat.EqMulDiv
import Lemma.Tensor.SEq0S.of.Eq
import Lemma.Tensor.EqAppend0S0
import Lemma.Tensor.EqCast_0'0.of.Eq
import Lemma.Tensor.Repeat.eq.Zero.of.Eq_0
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.EqCastS.of.SEq.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.EqSet.of.EqGet
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqMin.of.Lt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTake.eq.Get.of.Lt_Min
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector


@[main]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.resize ⟨0, by grind⟩ n =
    if h_n : s[0] < n then
      cast
        (congrArg (Tensor α) (by simp [EqAddMulDiv, Set_0.eq.Cons_Tail.of.GtLength_0 h]))
        (((cast
          (congrArg (Tensor α) (by simp [Set_0.eq.Cons_Tail.of.GtLength_0 h]))
          (X.repeat ⟨0, h⟩ (n / s[0]))) : Tensor α ((n / s[0]) * s[0] :: s.tail)) ++ (0 : Tensor α (n % s[0] :: s.tail))
        )
    else if h_n : s[0] > n then
      cast (congrArg (Tensor α) (by rw [Set_0.eq.Cons_Tail.of.GtLength_0 h])) (0 : Tensor α (n :: s.tail))
    else
      cast (congrArg (Tensor α) (by rw [EqSet.of.EqGet (by grind) (d := ⟨0, by grind⟩)])) X := by
-- proof
  unfold Tensor.resize
  simp
  match s with
  | [] =>
    nomatch h
  | k :: s =>
    simp
    split_ifs with h_n h_n
    ·
      rfl
    ·
      apply EqCast.of.SEq
      rw [Repeat.eq.Zero.of.Eq_0]
      .
        erw [EqCast_0'0.of.Eq (by grind)]
        rw [Tensor.EqAppend0S0]
        apply @Tensor.SEq0S.of.Eq
        simp [Nat.EqAddMulDiv]
      .
        rw [Div.eq.Zero.of.Lt h_n]
    ·
      have h_n : k = n := by omega
      subst h_n
      apply EqCastS.of.SEq.Eq
      ·
        grind
      ·
        rw [Repeat.eq.Cast.of.Eq_1]
        .
          erw [Tensor.EqCast_0'0.of.Eq (by grind)]
          rw [Tensor.EqAppend0S0]
          apply @Tensor.SEq0S.of.Eq
          simp [Nat.EqAddMulDiv]
          sorry
        .
          sorry
        apply SEq.of.SEqDataS.Eq
        ·
          simp [Nat.EqMulDiv]
        ·
          rw [DataFromVector.eq.FlattenMapData]
          apply SEq.of.All_EqGetS.Eq.fin
          ·
            intro t
            have h_t := t.isLt
            simp only [ProdCons.eq.Mul_Prod] at h_t
            let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
            let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
            erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
            erw [GetMap.eq.UFnGet]
            rw [GetTake.eq.Get.of.Lt_Min.fin]
            erw [GetToVector.eq.Get.cons.fin]
            erw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨q, by grind⟩)]
            ·
              simp
              erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              simp [h_qr]
            ·
              simp
          ·
            grind


-- created on 2026-07-09
