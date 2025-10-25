import Lemma.Bool.Ite.eq.IteNot
import Lemma.Nat.Min.eq.IteGe
open Bool Nat


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b = if a < b then
    a
  else
    b := by
-- proof
  rw [Ite.eq.IteNot]
  rw [Min.eq.IteGe]
  simp


-- created on 2025-05-07
