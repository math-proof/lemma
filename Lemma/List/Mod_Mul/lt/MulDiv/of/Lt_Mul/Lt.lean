import Lemma.List.DropSet.eq.Drop.of.Lt
import Lemma.List.ProdDrop.eq.MulProdDrop_Add_1.of.GtLength
import Lemma.List.ProdDrop.eq.MulProdSDrop.of.Le
import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.List.ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge
import Lemma.List.TakeEraseIdx.eq.Take.of.Gt
import Lemma.Nat.DivMulS.eq.Div.of.Ne_0
import Lemma.Nat.Mod_Mul.lt.MulDiv.of.Lt_Mul.Lt
import Lemma.Nat.MulMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Mul_Mul
open List Nat Fin


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
  {i : Fin s[d]}
  {k n t : ℕ}
-- given
  (h_k : k < d)
  (h_t : t < ((s.eraseIdx ↑d).take k).prod * (n * ((s.eraseIdx ↑d).drop (k + 1)).prod)) :
-- imply
  ((t / ((s.set k n).drop (↑d + 1)).prod * s[d] + ↑i) * (s.drop (↑d + 1)).prod + t % ((s.set k n).drop (↑d + 1)).prod) % (n * (s.drop (k + 1)).prod) < n * (s.drop (k + 1)).prod / (s.drop k).prod * (s.drop k).prod ↔
    t % (n * (((s.take ↑d).drop (k + 1)).prod * (s.drop (↑d + 1)).prod)) < n * ((s.eraseIdx ↑d).drop (k + 1)).prod / ((s.eraseIdx ↑d).drop k).prod * ((s.eraseIdx ↑d).drop k).prod := by
-- proof
  have h_i := i.isLt
  simp [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)] at h_t
  rw [TakeEraseIdx.eq.Take.of.Gt (by grind)] at h_t
  repeat rw [Mul_Mul.eq.MulMul] at h_t
  simp [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k + 1 by grind)]
  simp [ProdDropEraseIdx.eq.ProdAppendDropTake.of.Ge (show d ≥ k by grind)]
  simp [ProdDrop.eq.MulProdSDrop.of.Le (show k + 1 ≤ d by omega) s]
  simp [ProdDrop.eq.MulProdSDrop.of.Le (show k ≤ d by omega) s]
  rw [ProdDrop.eq.MulProdDrop_Add_1.of.GtLength d.isLt]
  repeat rw [Mul_Mul.eq.MulMul (c := s[d.val])]
  rw [DivMulS.eq.Div.of.Ne_0 (by grind)]
  rw [DropSet.eq.Drop.of.Lt (by grind)]
  rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength (s := s.take d) (i := k) (by grind)]
  erw [Mod_Mul.lt.MulDiv.of.Lt_Mul.Lt h_i h_t]


-- created on 2026-08-04
-- updated on 2026-08-05
