import Lemma.Int.EqAddSub
import Lemma.Int.Sub.ne.Zero.of.Ne
import Lemma.Rat.Add_Div.eq.DivAdd.of.Ne_0
import Lemma.Rat.Div1.eq.Inv
open Int Rat


@[main, comm]
private lemma main
  [DivisionRing α]
  {a : α}
-- given
  (h : a ≠ 1) :
-- imply
  (1 - a)⁻¹ = 1 + a / (1 - a) := by
-- proof
  rw [Add_Div.eq.DivAdd.of.Ne_0]
  ·
    rw [EqAddSub]
    rw [Inv.eq.Div1]
  ·
    apply Sub.ne.Zero.of.Ne h.symm


-- created on 2025-12-08
-- updated on 2025-12-09
