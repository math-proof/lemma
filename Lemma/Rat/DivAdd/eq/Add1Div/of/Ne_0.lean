import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.Div.eq.One.of.Ne_0
open Rat


@[main, comm]
private lemma main
  [DivisionSemiring α]
  {d : α}
-- given
  (h : d ≠ 0)
  (x : α):
-- imply
  (d + x) / d = 1 + x / d := by
-- proof
  rw [DivAdd.eq.AddDivS]
  rw [Div.eq.One.of.Ne_0 h]


-- created on 2025-03-25
