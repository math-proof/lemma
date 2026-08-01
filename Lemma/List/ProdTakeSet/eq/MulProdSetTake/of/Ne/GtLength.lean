import Lemma.List.EqSet.of.LeLength
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.SetAppend.eq.Append_Set.of.GtLength
import Lemma.List.Take.eq.AppendTake.of.GtLength
import Lemma.List.TakeSet.eq.SetTake.of.Lt
import Lemma.List.TakeSet.eq.Take.of.Ge
open List


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_s : s.length > j)
  (h_i : i ≠ j)
  (n : α) :
-- imply
  ((s.set i n).take (j + 1)).prod = ((s.take j).set i n).prod * s[j] := by
-- proof
  if h : i < j then
    have h_append : (s.set i n).take (j + 1) = (s.take j).set i n ++ [s[j]] := by
      rw [TakeSet.eq.SetTake.of.Lt (show i < j + 1 by omega)]
      rw [Take.eq.AppendTake.of.GtLength h_s]
      rw [SetAppend.eq.Append_Set.of.GtLength (show i < (s.take j).length by simp; omega)]
    rw [h_append, ProdAppend.eq.MulProdS]
    grind
  else
    have h_take : (s.set i n).take (j + 1) = s.take (j + 1) :=
      TakeSet.eq.Take.of.Ge (s := s) (i := i) (j := j + 1) (a := n) (by omega)
    have h_set : (s.take j).set i n = s.take j := by
      rw [EqSet.of.LeLength]; simp; omega
    rw [h_take, h_set, Take.eq.AppendTake.of.GtLength h_s, ProdAppend.eq.MulProdS]
    simp


-- created on 2026-07-31
