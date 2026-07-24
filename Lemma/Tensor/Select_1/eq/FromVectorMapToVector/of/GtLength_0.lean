import Lemma.Bool.EqCast.of.SEq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.LengthSlice.eq.ProdTake.of.GtGet.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.LengthSlice.eq.One.of.Lt
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.AddMul.lt.Mul.of.Lt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtLength
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α (n :: s))
  (i : Fin s[0]) :
-- imply
  X.select ⟨1, by grind⟩ ⟨i, by grind⟩ = Tensor.fromVector (X.toVector.map (·.select ⟨0, h⟩ ⟨i, by grind⟩)) := by
-- proof
  apply Eq.of.EqDataS
  conv_lhs => unfold Tensor.select; simp
  apply EqCast.of.SEq
  rw [DataFromVector.eq.FlattenMapData]
  simp only [GetElem.getElem]
  apply SEq.of.All_EqGetS.Eq.fin
  ·
    intro t
    have h_d : 1 < (n :: s).length := by grind
    have h_len_eq : (⟨i, n * (s.take 1).prod, s[0]⟩ : Slice).length (n * (s.take 1).prod) = n := by simpa using LengthSlice.eq.ProdTake.of.GtGet.GtLength.simp (s := n :: s) (d := 1) h_d i.isLt
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul t.isLt
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
    erw [GetGetSlice.eq.Get.of.GtGet.GtLength h_d i.isLt]
    simp only [GetElem.getElem]
    erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    conv_rhs =>
      simp only [GetElem.getElem]
      erw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨q, by grind⟩) (j := ⟨r, by grind⟩) (by grind)]
      simp only [GetElem.getElem]
      erw [GetMap.eq.UFnGet.of.Lt.fin (by grind)]
      erw [GetMap.eq.UFnGet.of.Lt.fin (by grind)]
      erw [GetToVector.eq.Get.fin (i := ⟨q, by grind⟩)]
      unfold Tensor.select
      simp only [GetElem.getElem]
      rw [DataGet.eq.GetUnflattenData.fin (X := X)]
    erw [GetCast.eq.Get.of.Eq.fin (by simpa using MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp h i.isLt) (i := ⟨r, by grind⟩)]
    have h_r : r < ((⟨i, ((n :: s).tail.take (0 + 1)).prod, ((n :: s).tail.get ⟨0, by grind⟩)⟩ : Slice).length ((n :: s).tail.take (0 + 1)).prod) * ((n :: s).tail.drop (0 + 1)).prod := by
      have h_mul := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp h i.isLt
      calc
        _ < (s.eraseIdx 0).prod := by grind
        _ = _ := by simpa using h_mul.symm
    let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r
    let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
    erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
    erw [GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by grind)]
    erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    erw [Vector.GetUnflatten.eq.Get_AddMul.fin]
    have h_slice_one : (⟨i, ((n :: s).tail.take (0 + 1)).prod, (n :: s).tail.get ⟨0, by grind⟩⟩ : Slice).length ((n :: s).tail.take (0 + 1)).prod = 1 := by
      simp [List.tail_cons]
      repeat rw [List.ProdTake_1.eq.Get_0.of.GtLength_0 (by grind)]
      simp
      apply LengthSlice.eq.One.of.Lt (n := s[0]) i.isLt
    congr 1
    simp only [show (qₐ : ℕ) = 0 by grind, show (rₐ : ℕ) = (r : ℕ) by grind]
    simp
    rw [Add_Add.eq.AddAdd]
    simp [Nat.add_mul]
    simp [Nat.mul_assoc]
    left
    simpa [ProdTake_1.eq.Get_0.of.GtLength_0 h] using (Prod.eq.MulProdS s 1).symm
  ·
    apply MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp (s := n :: s) (by grind) i.isLt


-- created on 2026-07-23
