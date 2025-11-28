import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.ProdEraseIdx.eq.MulProdS
open List


@[main]
private lemma simp
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d]) :
-- imply
  (⟨i, (s.take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod = (s.eraseIdx d).prod := by
-- proof
  rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength.simp h_d h_i]
  rw [ProdEraseIdx.eq.MulProdS]


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d]) :
-- imply
  (⟨i, ((List.map Nat.cast s).take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod = (s.eraseIdx d).prod := by
-- proof
  rw [List.ProdTakeMapCast.eq.CastProdTake]
  apply simp h_d h_i


-- created on 2025-11-15
