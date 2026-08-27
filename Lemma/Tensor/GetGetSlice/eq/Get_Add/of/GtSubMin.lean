import sympy.tensor.tensor
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten.of.Lt
import Lemma.Vector.EqUnflattenFlatten
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.Lt.of.Lt_Min
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.Fin.Eq.of.Val
open Tensor Vector List Nat Fin


@[main, fin]
private lemma main
  {m n j i : ℕ}
-- given
  (h_i : i < n ⊓ m - j)
  (X : Tensor α (m :: s)) :
-- imply
  have : i < (⟨j, n, 1⟩ : Slice).length m := by simp_all [LengthSlice.eq.SubMin]
  X[j:n][i] = X[j + i]'(Lt.of.Lt_Min (LtAdd.of.Lt_Sub.left h_i)) := by
-- proof
  unfold Tensor.getSlice
  simp
  simp [GetElem.getElem]
  rw [Tensor.get]
  rw [Tensor.toVector]
  simp [GetElem.getElem]
  simp [GetCast.eq.Get.of.Eq.fin]
  have h_m : m = X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 (by simp)]
    simp
  erw [GetMap.eq.UFnGet]
  apply Eq.of.EqDataS
  simp
  erw [GetSplitAt_1.eq.GetUnflatten.of.Lt.fin]
  erw [EqUnflattenFlatten]
  erw [GetMap.eq.UFnGet.of.Lt.fin]
  congr
  apply Eq.of.Val (b := ⟨j + i, by grind⟩)
  simp
  have h_idx := GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0 (a := (j : ℤ)) (b := (n : ℤ)) (d := 1) (N := X.length) (by decide) ⟨i, by simpa [← h_m, LengthSlice.eq.SubMin]⟩
  simp [EqAdd_Mul_DivSub1Sign_2] at h_idx
  simpa [GetElem.getElem] using h_idx


-- created on 2026-08-11
