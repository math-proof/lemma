module

public import Theorem.List.LengthSlice_Mul.eq.ProdTake.of.GtGet.GtLength
public import Theorem.List.ProdTake.eq.MulProdTake.of.GtLength

public section

open List


public theorem List.LengthSlice.eq.ProdTake.of.GtGet.GtLength.simp
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d]) :
-- imply
  (⟨i, (s.take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod = (s.take d).prod := by
-- proof
  repeat rw [ProdTake.eq.MulProdTake.of.GtLength]
  .
    simp_all [LengthSlice_Mul.eq.ProdTake.of.GtGet.GtLength h_d h_i]
  .
    exact h_d


public theorem List.LengthSlice.eq.ProdTake.of.GtGet.GtLength
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d]) :
-- imply
  (⟨i, ((List.map Nat.cast s).take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod = (s.take d).prod := by
-- proof
  rw [List.ProdTakeMapCast.eq.ProdTake]
  apply List.LengthSlice.eq.ProdTake.of.GtGet.GtLength.simp h_d h_i


-- created on 2025-11-15
