import Lemma.Nat.Le_SubMulS.of.Lt
import Lemma.Nat.EqMul_Div.of.Dvd
import Lemma.List.Dvd_ProdSet.of.Lt_Length
import Lemma.Nat.AddMul.lt.Mul
open List Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (i : Fin s[0])
  (j : Fin n) :
-- imply
  (s.set 0 (n * s[0])).prod / (n * s[0]) ≤ (s.set 0 (n * s[0])).prod - (j * s[0] + i) * ((s.set 0 (n * s[0])).prod / (n * s[0])) := by
-- proof
  have h_add_mul := AddMul.lt.Mul j i
  convert Le_SubMulS.of.Lt h_add_mul ((s.set 0 (n * s[0])).prod / (n * s[0]))
  rw [EqMul_Div.of.Dvd]
  apply Dvd_ProdSet.of.Lt_Length h


-- created on 2025-07-18
