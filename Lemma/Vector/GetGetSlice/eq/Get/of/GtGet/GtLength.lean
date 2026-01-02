import Lemma.List.Get.dvd.ProdTake.of.GtLength
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.ProdTake.eq.DivProdTake.of.Ne_0.GtLength
import Lemma.Nat.LtAddMul.of.Lt.Lt_Div.Dvd
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtProdTake.GtLength
open List Nat Vector


@[main]
private lemma main
  {s : List ℕ}
  {j : ℕ}
-- given
  (h_d : d < s.length)
  (h_j : j < s[d])
  (v : List.Vector α (s.take (d + 1)).prod)
  (i : Fin ((⟨j, (s.take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod)):
-- imply
  have h_length_slice := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength.simp h_d h_j
  have h_i : i < (s.take d).prod := by
    have h_i := i.isLt
    simp_all
  have h_div := DivProdTake.eq.ProdTake.of.Ne_0.GtLength h_d (by grind)
  have h_d := Get.dvd.ProdTake.of.GtLength h_d
  (v.getSlice ⟨j, (s.take (d + 1)).prod, s[d]⟩).get i = v.get ⟨i * s[d] + j, LtAddMul.of.Lt.Lt_Div.Dvd h_d (by simp_all) h_j⟩ := by
-- proof
  intro h_length_slice h_i h_div h_d
  apply GetGetSlice.eq.Get.of.GtGet.GtProdTake.GtLength _ h_i h_j v


-- created on 2026-01-02
