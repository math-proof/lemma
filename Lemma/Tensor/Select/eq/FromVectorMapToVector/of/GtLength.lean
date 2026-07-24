import Lemma.Bool.EqCast.of.SEq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.LengthSlice.eq.ProdTake.of.GtGet.GtLength
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdTake_Add_1.eq.MulProdTake.of.GtLength
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Div.eq.AddMulDiv_Mul
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtLength
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector
set_option maxHeartbeats 800000


@[main]
private lemma main
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α (n :: s))
  (i : Fin s[d]) :
-- imply
  X.select ⟨d + 1, by grind⟩ ⟨i, by grind⟩ = Tensor.fromVector (X.toVector.map (·.select ⟨d, h⟩ ⟨i, by grind⟩)) := by
-- proof
  apply Eq.of.EqDataS
  conv_lhs => unfold Tensor.select; simp
  apply EqCast.of.SEq
  rw [DataFromVector.eq.FlattenMapData]
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_d : d + 1 < (n :: s).length := by grind
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul t.isLt
    let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
    erw [GetGetSlice.eq.Get.of.GtGet.GtLength h_d i.isLt]
    simp only [GetElem.getElem]
    erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    have h_t : t < ((n :: s).headD 1) * (s.eraseIdx d).prod := by grind [t.isLt, MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp (s := n :: s) (d := d + 1) h_d i.isLt]
    let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
    erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
    erw [GetMap.eq.UFnGet.of.Lt.fin (by grind)]
    erw [GetMap.eq.UFnGet.of.Lt.fin (by grind)]
    erw [GetToVector.eq.Get.fin (i := ⟨q', by grind⟩)]
    unfold Tensor.select
    simp
    rw [DataGet.eq.GetUnflattenData.fin (X := X)]
    erw [GetCast.eq.Get.of.Eq.fin (MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp h i.isLt) (i := ⟨r', by grind⟩)]
    simp
    have h_r : r' < ((⟨↑↑i, ↑(s.take (d + 1)).prod, ↑s[d]⟩ : Slice).length (s.take (d + 1)).prod) * (s.drop (d + 1)).prod := by
      apply Nat.lt_of_lt_of_eq r'.isLt
      apply ProdEraseIdx.eq.MulLengthSlice.of.GtGet.GtLength.simp h i.isLt
    let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r
    let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
    erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
    erw [GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by grind)]
    erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    erw [GetUnflatten.eq.Get_AddMul.fin]
    congr 1
    simp only [h_qₐ_div, h_rₐ_mod]
    simp [h_r'_mod, h_r_mod]
    rw [Add_Add.eq.AddAdd]
    simp [Nat.add_mul, Nat.mul_assoc]
    grind [AddMulDiv_Mul.eq.Div, ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength h, Prod.eq.MulProdS s (d + 1), ProdTake_Add_1.eq.MulProdTake.of.GtLength h]
  ·
    apply MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp (s := n :: s) (by grind) i.isLt


-- created on 2026-07-23
-- updated on 2026-07-24
