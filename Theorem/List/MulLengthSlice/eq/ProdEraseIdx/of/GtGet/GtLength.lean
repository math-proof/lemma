module

public import Initialize.Tactic.Attr.Basic

public import Theorem.List.LengthSlice.eq.ProdTake.of.GtGet.GtLength
public import Theorem.List.ProdEraseIdx.eq.MulProdS

public section

open List


@[comm]
public theorem List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d]) :
-- imply
  (⟨i, (s.take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod = (s.eraseIdx d).prod := by
-- proof
  rw [LengthSlice.eq.ProdTake.of.GtGet.GtLength.simp h_d h_i]
  rw [ProdEraseIdx.eq.MulProdS]


@[comm]
public theorem List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d]) :
-- imply
  (⟨i, ((List.map Nat.cast s).take (d + 1)).prod, s[d]⟩ : Slice).length (s.take (d + 1)).prod * (s.drop (d + 1)).prod = (s.eraseIdx d).prod := by
-- proof
  rw [List.ProdTakeMapCast.eq.ProdTake]
  apply List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp h_d h_i


-- created on 2025-11-15
