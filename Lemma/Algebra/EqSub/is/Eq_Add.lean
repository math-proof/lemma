import Lemma.Algebra.EqSub.of.EqAdd
import Lemma.Algebra.EqSubAdd
import Lemma.Algebra.EqAddS.is.Eq
open Algebra


@[main, comm, mp, mpr, mp.comm, mpr.comm]
private lemma left
  [AddCommGroup α]
-- given
  (d x y : α) :
-- imply
  y - d = x ↔ y = d + x := by
-- proof
  constructor <;>
    intro h
  ·
    have h := EqAddS.of.Eq d h
    simp at h
    rw [Add.comm] at h
    exact h
  ·
    rw [h]
    rw [EqSubAdd.left]


@[main, comm, mp, mpr, mp.comm, mpr.comm]
private lemma main
  [AddGroup α]
-- given
  (d x y : α) :
-- imply
  y - x = d ↔ y = d + x := by
-- proof
  constructor <;>
    intro h
  ·
    have h := EqAddS.of.Eq x h
    simp at h
    exact h
  ·
    exact (Eq_Sub.of.EqAdd h.symm).symm

-- created on 2025-04-26
