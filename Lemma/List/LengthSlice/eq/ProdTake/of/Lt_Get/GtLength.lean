import Lemma.List.LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d]) :
-- imply
  (⟨i, ((List.map Nat.cast s).take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod = (s.take d).prod := by
-- proof
  repeat rw [ProdTake.eq.MulProdTake.of.GtLength]
  .
    simp_all [LengthSlice_Mul.eq.ProdTake.of.Lt_Get.GtLength h_d h_i]
  .
    exact h_d
  .
    simpa



-- created on 2025-11-15
