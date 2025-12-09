import Lemma.Rat.Div1.eq.Inv
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
  a - b⁻¹ = (a * b - 1) / b := by
-- proof
  rw [Inv.eq.Div1]
  rw [Sub_Div.eq.DivSubMul.of.Ne_0 h]


-- created on 2025-12-08
