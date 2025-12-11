import Lemma.Nat.EqMul1
import Lemma.Rat.Add_Inv.eq.DivAddMul.of.Ne_0
open Nat Rat


@[main, comm]
private lemma main
  [DivisionRing α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  1 + a⁻¹ = (a + 1) / a := by
-- proof
  rw [Add_Inv.eq.DivAddMul.of.Ne_0 h]
  rw [EqMul1]


-- created on 2025-12-09
