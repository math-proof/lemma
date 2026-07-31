import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.SetAppend.eq.Append_Set.of.GtLength
import Lemma.List.Take.eq.AppendTake.of.GtLength
import Lemma.List.TakeSet.eq.SetTake.of.Lt
open List


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_s : s.length > j)
  (h_i : i < j)
  (n : α) :
-- imply
  ((s.set i n).take (j + 1)).prod = ((s.take j).set i n).prod * s[j] := by
-- proof
  have h_append : (s.set i n).take (j + 1) = (s.take j).set i n ++ [s[j]] := by
    rw [TakeSet.eq.SetTake.of.Lt (show i < j + 1 by omega)]
    rw [Take.eq.AppendTake.of.GtLength h_s]
    rw [SetAppend.eq.Append_Set.of.GtLength (show i < (s.take j).length by simp; omega)]
  rw [h_append, ProdAppend.eq.MulProdS]
  grind


-- created on 2026-07-31
