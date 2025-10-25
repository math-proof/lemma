import Lemma.Nat.Min.eq.IteLe
import Lemma.Bool.Ite.eq.IteNot
open Bool Nat


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b = if a > b then
    b
  else
    a := by
-- proof
  rw [Ite.eq.IteNot]
  rw [Min.eq.IteLe]
  simp


-- created on 2025-05-07
