import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.Take.eq.AppendTake.of.GtLength
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  (s.take (i + 1)).prod = (s.take i).prod * s[i] := by
-- proof
  rw [Take.eq.AppendTake.of.GtLength h]
  rw [ProdAppend.eq.MulProdS]
  simp


-- created on 2025-10-27
