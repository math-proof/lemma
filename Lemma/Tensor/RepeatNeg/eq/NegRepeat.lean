import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.DataRepeat.eq.Cast_FlattenMapSplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetNeg.eq.NegGet
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SplitAtNeg.eq.NegSplitAt
import sympy.tensor.functions
open Bool Fin List Tensor Vector


@[main]
private lemma main
  [Neg α]
-- given
  (X : Tensor α s)
  (n : ℕ)
  (d : Fin s.length) :
-- imply
  (-X).repeat n d = -X.repeat n d := by
-- proof
  apply Eq.of.EqDataS
  rw [DataNeg.eq.NegData]
  simp [DataRepeat.eq.Cast_FlattenMapSplitAtData]
  have h_prod := ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength d.isLt n
  symm at h_prod
  apply EqCast.of.SEq.Eq h_prod
  rw [DataNeg.eq.NegData]
  rw [SplitAtNeg.eq.NegSplitAt]
  apply SEq.of.All_EqGetS.Eq.fin h_prod
  intro t
  have h_t := t.isLt
  rw [GetNeg.eq.NegGet.fin]
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
  rw [GetCast.eq.Get.of.Eq.fin h_prod ]
  simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
  simp [GetRepeat.eq.Get_Mod.fin]
  simp [GetNeg.eq.NegGet.fin]


-- created on 2025-12-04
