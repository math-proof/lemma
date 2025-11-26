import Lemma.List.TakeDrop.eq.Cons_TakeDrop.of.GtLength
import Lemma.Nat.Mul
open List Nat


@[main, comm]
private lemma main
  [One α] [CommMagma α]
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  ((s.drop i).take (d + 1)).prod = ((s.drop (i + 1)).take d).prod * s[i] := by
-- proof
  simp [TakeDrop.eq.Cons_TakeDrop.of.GtLength h]
  rw [Mul.comm]


-- created on 2025-10-24
