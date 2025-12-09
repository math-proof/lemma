import Lemma.Nat.DivAddMul.eq.Add_Div.of.Ne_0
import Lemma.Rat.Add_Div.eq.DivAddMul.of.Ne_0
import Lemma.Rat.Div1.eq.Inv
open Nat Rat


@[main, comm]
private lemma main
  [DivisionRing α]
  {b : α}
-- given
  (h : b ≠ 0)
  (a : α) :
-- imply
  a + b⁻¹ = (a * b + 1) / b := by
-- proof
  rw [Inv.eq.Div1]
  rw [Add_Div.eq.DivAddMul.of.Ne_0 h]


-- created on 2025-12-09
