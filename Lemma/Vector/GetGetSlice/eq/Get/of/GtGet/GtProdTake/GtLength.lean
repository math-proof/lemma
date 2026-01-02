import Lemma.List.ProdTake.eq.DivProdTake.of.Ne_0.GtLength
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.Get.dvd.ProdTake.of.GtLength
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.List.LengthSlice.eq.Div.of.Lt.Dvd
import Lemma.Nat.Any_Eq_Mul.of.Dvd
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.LtAddMul.of.Lt.Lt_Div.Dvd
import Lemma.Vector.GetGetSlice.eq.Get
import sympy.vector.vector
open List Nat Vector


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : d < s.length)
  (h_i : i < (s.take d).prod)
  (h_j : j < s[d])
  (v : List.Vector α (s.take (d + 1)).prod) :
-- imply
  have h_length_slice := LengthSlice.eq.ProdTake.of.Lt_Get.GtLength.simp h_d h_j
  have h_div := List.DivProdTake.eq.ProdTake.of.Ne_0.GtLength h_d (by grind)
  have h_d := Get.dvd.ProdTake.of.GtLength h_d
  v[j : (s.take (d + 1)).prod : s[d]].get ⟨i, by rwa [h_length_slice]⟩ = v.get ⟨i * s[d] + j, LtAddMul.of.Lt.Lt_Div.Dvd h_d (by rwa [h_div]) h_j⟩ := by
-- proof
  intro h_length_slice h_div h_d
  apply GetGetSlice.eq.Get.of.Lt.Lt.Dvd h_d _ h_j v
  rwa [h_div]


-- created on 2026-01-02
