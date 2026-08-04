import Lemma.Nat.Mod_Mul.lt.MulDiv.of.Mod_Mul.lt.MulDiv.Lt_Mul.Lt
import Lemma.Nat.MulMul
import Lemma.Nat.EqMulDiv.of.Dvd
import Lemma.Nat.Mul_Mul
import Lemma.Nat.Dvd_Mul
import Lemma.Nat.DivMul.eq.MulDiv.of.Dvd
import Lemma.List.ProdTake.eq.MulProdS.of.Ge
import Lemma.List.ProdTake.eq.Mul_ProdDropTake.of.Ge
import Lemma.Nat.DivMulS.eq.Div.of.Ne_0
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.ProdDrop.eq.MulProdDrop_Add_1.of.GtLength
import Lemma.List.AddMul_ProdDrop.lt.ProdDrop.of.GtProdDrop_Succ.GtGet.Gtlength
import Lemma.List.DropSet.eq.Drop.of.Lt
import Lemma.List.EraseIdxSet.eq.SetEraseIdx.of.Lt
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge
import Lemma.List.ProdDropTake.eq.MulProdDropTake.of.Gt.GtLength
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.TakeEraseIdx.eq.Take.of.Gt
import Lemma.List.GetTake.eq.Get.of.GtLengthTake
import Lemma.List.GetSet.eq.Get.of.Lt.GtLength
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.Lt.of.Lt.Le
import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.Mod_Mul.eq.Add_Mul_ModDiv
import Lemma.Nat.Mod_Mul.eq.AddMul_Mod.of.Lt
import Lemma.Nat.MulDivMulS.eq.Mul_MulDivMulS
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.AddAdd.eq.Add_Add
open Nat List Fin


/--
| attributes | lemma |
| :---: | :---: |
| main | List.Mod_Mul.lt.MulDiv.of.Mod_Mul.lt.MulDiv.Lt_Mul.Lt |
| mpr | List.Mod_Mul.lt.MulDiv.of.Mod_Mul.lt.MulDiv.Lt_Mul.mpr |
-/
@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
  {i : Fin s[d]}
  {k n t : ℕ}
-- given
  (h_k : k < d)
  (h_t : t < ((s.eraseIdx ↑d).take k).prod * (n * ((s.eraseIdx ↑d).drop (k + 1)).prod))
  (h_r : ((t / ((s.set k n).drop (↑d + 1)).prod * s[d] + ↑i) * (s.drop (↑d + 1)).prod + t % ((s.set k n).drop (↑d + 1)).prod) % (n * (s.drop (k + 1)).prod) < n * (s.drop (k + 1)).prod / (s.drop k).prod * (s.drop k).prod):
-- imply
  t % (n * (((s.take ↑d).drop (k + 1)).prod * (s.drop (↑d + 1)).prod)) < n * ((s.eraseIdx ↑d).drop (k + 1)).prod / ((s.eraseIdx ↑d).drop k).prod * ((s.eraseIdx ↑d).drop k).prod := by
-- proof
  simp [List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)]
  simp [List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k by grind)]
  simp [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega) s] at h_r
  simp [ProdDrop.eq.MulProdSDrop.of.Le (show k ≤ d by omega) s] at h_r
  rw [List.ProdDrop.eq.MulProdDrop_Add_1.of.GtLength d.isLt] at h_r
  repeat rw [Mul_Mul.eq.MulMul (c := s[d.val])] at h_r
  rw [DivMulS.eq.Div.of.Ne_0 (by grind)] at h_r
  rw [List.DropSet.eq.Drop.of.Lt (by grind)] at h_r
  simp [List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)] at h_t
  rw [List.TakeEraseIdx.eq.Take.of.Gt (by grind)] at h_t
  have h_drop_take := List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (s := s.take ↑d) (i := k) (by grind)
  rw [List.GetTake.eq.Get.of.GtLengthTake (by grind)] at h_drop_take
  rw [h_drop_take] at h_r ⊢
  have h_take_d := List.ProdTake.eq.Mul_ProdDropTake.of.Ge (show k ≤ d by grind) (s := s)
  rw [h_drop_take] at h_take_d
  set D := (s.drop (↑d + 1)).prod with h_D
  set M := ((s.take ↑d).drop (k + 1)).prod with h_M
  have h_take_k : (s.take k).prod = (s.take ↑d).prod / (s[k] * M) := by
    rw [h_take_d]
    rw [EqDivMul.of.Ne_0 (by grind)]
  rw [h_take_k] at h_t
  rw [Div_Mul.eq.DivDiv.comm] at h_t
  rw [Nat.MulDiv.eq.DivMul.of.Dvd, Mul_Mul.comm (a := n), Mul_Mul.eq.MulMul, EqMulDiv.of.Dvd] at h_t
  .
    set K := (s.take k).prod with h_K
    rw [h_take_d] at h_t
    rw [Mul_Mul.eq.MulMul.comm (a := K)] at h_t
    rw [MulMul.comm] at h_t
    rw [EqDivMul.of.Ne_0 (by grind)] at h_t
    rw [Mul_Mul.eq.MulMul, MulMul.comm (a := K)] at h_t
    apply Nat.Mod_Mul.lt.MulDiv.of.Mod_Mul.lt.MulDiv.Lt_Mul.Lt i.isLt h_t h_r
  .
    rw [h_take_d, Mul_Mul.eq.MulMul]
    apply Nat.Dvd_Mul
  .
    rw [h_take_d, Mul_Mul.eq.MulMul, EqDivMul.of.Ne_0 (by grind)]
    apply Nat.Dvd_Mul


/--
| attributes | lemma |
| :---: | :---: |
| mpr | List.Mod_Mul.lt.MulDiv.of.Mod_Mul.lt.MulDiv.Lt_Mul.mpr |
-/
@[main]
private lemma mpr
  {s : List ℕ}
  {d : Fin s.length}
  {i : Fin s[d]}
  {k n t : ℕ}
-- given
  (h_k : k < d)
  (h_t : t < ((s.eraseIdx ↑d).take k).prod * (n * ((s.eraseIdx ↑d).drop (k + 1)).prod))
  (h_r' : t % (n * (((s.take ↑d).drop (k + 1)).prod * (s.drop (↑d + 1)).prod)) < n * ((s.eraseIdx ↑d).drop (k + 1)).prod / ((s.eraseIdx ↑d).drop k).prod * ((s.eraseIdx ↑d).drop k).prod) :
-- imply
  ((t / ((s.set k n).drop (↑d + 1)).prod * s[d] + ↑i) * (s.drop (↑d + 1)).prod + t % ((s.set k n).drop (↑d + 1)).prod) % (n * (s.drop (k + 1)).prod) < n * (s.drop (k + 1)).prod / (s.drop k).prod * (s.drop k).prod := by
-- proof
  simp [List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)] at ⊢
  simp [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega) s] at ⊢
  simp [ProdDrop.eq.MulProdSDrop.of.Le (show k ≤ d by omega) s] at ⊢
  rw [List.ProdDrop.eq.MulProdDrop_Add_1.of.GtLength d.isLt] at ⊢
  repeat rw [Mul_Mul.eq.MulMul (c := s[d.val])] at ⊢
  rw [DivMulS.eq.Div.of.Ne_0 (by grind)] at ⊢
  rw [List.DropSet.eq.Drop.of.Lt (show k < ↑d + 1 by omega)] at ⊢
  simp [List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)] at h_t h_r'
  rw [List.TakeEraseIdx.eq.Take.of.Gt (by grind)] at h_t
  have h_drop_take := List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (s := s.take ↑d) (i := k) (by grind)
  rw [List.GetTake.eq.Get.of.GtLengthTake (by grind)] at h_drop_take
  rw [h_drop_take] at h_r' ⊢
  have h_take_d := List.ProdTake.eq.Mul_ProdDropTake.of.Ge (show k ≤ d by grind) (s := s)
  rw [h_drop_take] at h_take_d
  set D := (s.drop (↑d + 1)).prod with h_D
  set M := ((s.take ↑d).drop (k + 1)).prod with h_M
  have h_take_k : (s.take k).prod = (s.take ↑d).prod / (s[k] * M) := by
    rw [h_take_d]
    rw [EqDivMul.of.Ne_0 (by grind)]
  rw [h_take_k] at h_t
  rw [Div_Mul.eq.DivDiv.comm] at h_t
  rw [Nat.MulDiv.eq.DivMul.of.Dvd, Mul_Mul.comm (a := n), Mul_Mul.eq.MulMul, EqMulDiv.of.Dvd] at h_t
  .
    set K := (s.take k).prod with h_K
    rw [h_take_d] at h_t
    rw [Mul_Mul.eq.MulMul.comm (a := K)] at h_t
    rw [MulMul.comm] at h_t
    rw [EqDivMul.of.Ne_0 (by grind)] at h_t
    rw [Mul_Mul.eq.MulMul, MulMul.comm (a := K)] at h_t
    apply Nat.Mod_Mul.lt.MulDiv.of.Mod_Mul.lt.MulDiv.Lt_Mul.Lt i.isLt h_t h_r'
  .
    rw [h_take_d, Mul_Mul.eq.MulMul]
    apply Nat.Dvd_Mul
  .
    rw [h_take_d, Mul_Mul.eq.MulMul, EqDivMul.of.Ne_0 (by grind)]
    apply Nat.Dvd_Mul


-- created on 2026-08-04
