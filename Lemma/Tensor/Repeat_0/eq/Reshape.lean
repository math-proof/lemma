import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.ProdSet__Mul_Get.eq.Mul_Prod.of.GtLength
import Lemma.List.Set_0.eq.Cons_Tail.of.GtLength_0
import Lemma.Nat.MulDivMul.eq.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector Fin


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s.length > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.repeat ⟨0, h_s⟩ n ≃ X.reshape (n * s[0] :: s.tail) (by simp [MulMul.eq.Mul_Mul, Prod.eq.Mul_ProdTail.of.GtLength_0 h_s]) := by
-- proof
  unfold Tensor.repeat Tensor.reshape
  simp
  apply SEq.of.SEqDataS.Eq
  ·
    rwa [Set_0.eq.Cons_Tail.of.GtLength_0]
  ·
    simp
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      simp
      rw [ProdSet__Mul_Get.eq.Mul_Prod.of.GtLength]
    ·
      rw [MulMul.eq.Mul_Mul, ← Prod.eq.Mul_ProdTail.of.GtLength_0 h_s]
      apply MulDivMul.eq.Mul
    ·
      apply SEq.of.All_EqGetS.Eq.fin
      ·
        intro i
        have h_i := i.isLt
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by grind⟩) (j := ⟨i, by grind⟩) (by simp)]
        rw [GetMap.eq.UFnGet]
        repeat rw [GetRepeat.eq.Get_Mod.fin]
        erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        simp
      ·
        rw [MulMul.eq.Mul_Mul, ← Prod.eq.Mul_ProdTail.of.GtLength_0 h_s]
        simp [MulDivMul.eq.Mul]


-- created on 2026-07-10
