import sympy.tensor.tensor
import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqGetCons
import Lemma.List.EqSet.of.EqGet
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.DivMulS.eq.Div.of.Ne_0
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.EqMulDiv
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.Ne_0.of.GtMul
import Lemma.Tensor.DataRepeat.as.FlattenMapSplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetFlatten.eq.Get.of.Lt_Mul
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetResize.eq.Ite_Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.resize ⟨0, by grind⟩ n ≃ ((cast (congrArg (Tensor α) (by simp [Set_0.eq.Cons_Tail.of.GtLength_0 h])) (X.repeat ⟨0, h⟩ (n / s[0]))) : Tensor α ((n / s[0]) * s[0] :: s.tail)) ++ (0 : Tensor α (n % s[0] :: s.tail)) := by
-- proof
  unfold Tensor.resize
  simp
  match s with
  | [] =>
    nomatch h
  | k :: s =>
    simp
    apply SEq.of.SEqDataS.Eq (by simp [EqAddMulDiv])
    simp
    apply SEq_Cast.of.SEq.Eq
    ·
      simp [MulAdd.eq.AddMulS]
    ·
      apply SEqCast.of.SEq.Eq (by simp)
      rw [EqData0'0]
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro t
        have h_t := t.isLt
        erw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by grind⟩) (j := ⟨t, by grind⟩) (by grind)]
        erw [GetMap.eq.UFnGet]
        simp [GetResize.eq.Ite_Get_Mod.fin]
        simp at h_t
        have h_ne_0 := Ne_0.of.GtMul h_t
        split_ifs with h_lt
        ·
          rw [Head.eq.Get_0.fin]
          erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp
          rw [DivMulS.eq.Div.of.Ne_0 (by grind)] at h_lt
          erw [GetAppend.eq.Get.of.Lt.fin (i := t) _ (X.repeat 0 (n / k)).data]
          ·
            rw [DataRepeat.eq.Cast_FlattenMapSplitAtData]
            rw [GetCast.eq.Get.of.Eq.fin (by grind)]
            simp
            rw [GetFlatten.eq.Get.of.Lt_Mul (by grind)]
            simp [GetRepeat.eq.Get_Mod.fin]
            erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            congr 1
            aesop
          ·
            simp
            erw [EqGetCons k s]
            grind
        ·
          rw [DivMulS.eq.Div.of.Ne_0 (by grind)] at h_lt
          erw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by grind) (by simpa [AddMulS.eq.MulAdd, EqAddMulDiv])]
          rw [EqGet0_0.fin]
      ·
        simp [AddMulS.eq.MulAdd, EqAddMulDiv]


-- created on 2026-07-09
-- updated on 2026-07-13
