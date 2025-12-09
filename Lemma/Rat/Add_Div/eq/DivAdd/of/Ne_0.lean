import Lemma.Rat.Add_Div.eq.DivAddMul.of.Ne_0
open Rat


@[main, comm]
private lemma main
  [DivisionRing α]
  {b : α}
-- given
  (h : b ≠ 0)
  (a : α) :
-- imply
  1 + a / b = (b + a) / b := by
-- proof
  rw [Add_Div.eq.DivAddMul.of.Ne_0 h]
  simp


-- created on 2025-12-09
