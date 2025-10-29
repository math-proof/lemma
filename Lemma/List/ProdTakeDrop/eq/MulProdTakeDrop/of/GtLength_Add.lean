import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.TakeDrop.eq.AppendTakeDrop.of.GtLength_Add
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : i + d < s.length) :
-- imply
  ((s.drop i).take (d + 1)).prod = ((s.drop i).take d).prod * s[i + d] := by
-- proof
  simp [TakeDrop.eq.AppendTakeDrop.of.GtLength_Add h]


-- created on 2025-10-29
