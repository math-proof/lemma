import Lemma.List.Prod.eq.MulProdS
import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main]
private lemma main
  [Monoid α]
-- given
  (h : i ≥ j)
  (s : List α) :
-- imply
  (s.take i).prod = (s.take j).prod * ((s.take i).drop j).prod := by
-- proof
  rw [Prod.eq.MulProdS (s.take i) j]
  rw [TakeTake.eq.Take.of.Ge (by assumption)]


-- created on 2025-11-28
