import Lemma.Algebra.EqSubS.is.Eq
import Lemma.Algebra.EqSubAdd
import Lemma.Algebra.EqSubS.of.Eq
open Algebra


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
