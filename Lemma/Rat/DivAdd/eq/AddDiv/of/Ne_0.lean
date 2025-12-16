import Lemma.Nat.Add
import Lemma.Rat.DivAdd.eq.Add1Div.of.Ne_0
open Rat Nat


@[main, comm]
private lemma main
  [DivisionSemiring α]
  {d : α}
-- given
  (h : d ≠ 0)
  (x : α) :
-- imply
  (x + d) / d = x / d + 1 := by
-- proof
  rw [Add.comm]
  rw [DivAdd.eq.Add1Div.of.Ne_0 h]
  rw [Add.comm]


-- created on 2025-12-16
