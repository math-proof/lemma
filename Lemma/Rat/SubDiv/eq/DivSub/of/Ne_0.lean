import Lemma.Rat.SubDiv.eq.DivSub_Mul.of.Ne_0
open Rat


@[main, comm]
private lemma main
  [DivisionRing α]
  {b : α}
-- given
  (h : b ≠ 0)
  (a : α) :
-- imply
  a / b - 1 = (a - b) / b := by
-- proof
  have := SubDiv.eq.DivSub_Mul.of.Ne_0 h (a := a) (x := 1)
  simp at this
  exact this


-- created on 2025-12-10
