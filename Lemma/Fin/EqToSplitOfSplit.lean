import Lemma.Fin.OfSplit.eq.Ite_Mul2
import Lemma.Fin.ToSplit.eq.Ite_Div_2
open Fin


@[main]
private lemma main
-- given
  (k : Fin (d + d)) :
-- imply
  k.ofSplit.toSplit = k := by
-- proof
  apply Fin.ext
  rw [ToSplit.eq.Ite_Div_2, OfSplit.eq.Ite_Mul2]
  grind


-- created on 2026-09-05
