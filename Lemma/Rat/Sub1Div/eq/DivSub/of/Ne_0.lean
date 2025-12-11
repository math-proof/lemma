import Lemma.Rat.Sub_Div.eq.DivSubMul.of.Ne_0
open Rat


@[main, comm]
private lemma main
  [DivisionRing α]
  {b : α}
-- given
  (h : b ≠ 0)
  (a : α) :
-- imply
  1 - a / b = (b - a) / b := by
-- proof
  have := Sub_Div.eq.DivSubMul.of.Ne_0 h 1 a
  simp at this
  assumption


-- created on 2025-12-11
