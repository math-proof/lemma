import Lemma.Int.EqSubS.is.Eq
import Lemma.Int.EqSubAdd
import Lemma.Nat.EqSubS.of.Eq
open Int Nat


@[main, comm]
private lemma main
  [AddGroup α]
  {x y d : α}
-- given
  (h : d + x = y) :
-- imply
  y - x = d := by
-- proof
  have h := EqSubS.of.Eq x h
  rw [EqSubAdd] at h
  simp_all


-- created on 2025-10-08
