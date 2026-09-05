import Lemma.Fin.OfSplit.eq.Ite_Mul2
import Lemma.Fin.ToSplit.eq.Ite_Div_2
open Fin


@[main]
private lemma main
-- given
  (j : Fin (d + d)) :
-- imply
  ofSplit (toSplit j) = j := by
-- proof
  apply Fin.ext
  rw [OfSplit.eq.Ite_Mul2, ToSplit.eq.Ite_Div_2]
  grind


-- created on 2026-09-05
