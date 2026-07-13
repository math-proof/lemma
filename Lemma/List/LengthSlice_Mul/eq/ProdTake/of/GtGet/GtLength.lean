import Lemma.List.EqLengthSlice_Mul.of.Lt
import Lemma.List.ProdTakeMapCast.eq.ProdTake
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d]) :
-- imply
  (⟨i, ((List.map Nat.cast s).take d).prod * s[d], s[d]⟩ : Slice).length ((s.take d).prod * s[d]) = (s.take d).prod := by
-- proof
  rw [ProdTakeMapCast.eq.ProdTake]
  rw [EqLengthSlice_Mul.of.Lt (by omega)]


-- created on 2025-11-15
