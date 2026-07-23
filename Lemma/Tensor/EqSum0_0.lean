import Lemma.Bool.EqCast.of.SEq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.EqGet0_0
import Lemma.Vector.EqSplitAt0_0
import Lemma.Vector.EqSum_0
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector


@[main]
private lemma main
  [AddZeroClass α]
-- given
  (s : List ℕ)
  (d : ℕ) :
-- imply
  (0 : Tensor α s).sum d = 0 := by
-- proof
  unfold Tensor.sum
  rw [EqData0'0]
  rw [EqSplitAt0_0]
  apply Eq.of.EqDataS
  simp
  rw [EqData0'0]
  apply EqCast.of.SEq
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_t := t.isLt
    rw [@Vector.EqGet0_0.fin]
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
    simp
    rw [@Vector.EqGet0_0.fin]
    rw [EqSplitAt0_0]
    rw [EqSum_0]
    rw [@Vector.EqGet0_0.fin]
  ·
    simp [ProdEraseIdx.eq.MulProdS]


-- created on 2026-07-23
