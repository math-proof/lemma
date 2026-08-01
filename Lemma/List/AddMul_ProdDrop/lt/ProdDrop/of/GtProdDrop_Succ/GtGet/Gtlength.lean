import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
open List Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : d < s.length)
  (h_i : i < s[d])
  (h_r : r < (s.drop (d + 1)).prod) :
-- imply
  i * (s.drop (d + 1)).prod + r < (s.drop d).prod := by
-- proof
  conv_rhs => rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength h_d]
  apply AddMul.lt.Mul.of.Lt.Lt
  ·
    grind
  ·
    grind


-- created on 2026-08-01
