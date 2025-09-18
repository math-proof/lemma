import Lemma.Algebra.EqSubS.is.Eq
import Lemma.Algebra.EqSubAdd
open Algebra


@[main, comm]
private lemma nat
  {x y d : ℕ}
-- given
  (h : d + x = y) :
-- imply
  y - x = d := by
-- proof
  rw [← h]
  rw [EqSubAdd.int]


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


-- created on 2025-04-16
