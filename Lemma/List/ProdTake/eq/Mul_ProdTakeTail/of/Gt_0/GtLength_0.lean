import Lemma.List.ProdTake.eq.Mul_ProdTakeTail.of.GtLength_0
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
  [Mul α] [One α]
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length > 0)
  (h_i : i > 0) :
-- imply
  (s.take i).prod = s[0] * (s.tail.take (i - 1)).prod := by
-- proof
  have := ProdTake.eq.Mul_ProdTakeTail.of.GtLength_0 h (i - 1)
  simp at this
  rwa [EqAddSub.of.Ge h_i] at this


-- created on 2025-07-05
-- updated on 2026-07-13
