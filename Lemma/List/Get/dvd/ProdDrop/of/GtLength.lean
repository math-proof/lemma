import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength
import Lemma.Nat.Dvd_Mul
open List Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s[i] ∣ (s.drop i).prod := by
-- proof
  rw [ProdDrop.eq.Mul_ProdDrop_Add_1.of.GtLength h]
  apply Dvd_Mul.left


-- created on 2026-04-16
