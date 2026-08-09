import Lemma.Int.In_Icc.is.InAdd
import Lemma.Int.In_Icc.is.InSub
import Lemma.Int.EqAddSub
import Lemma.Int.EqSubAdd
open Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.InSub.is.In_Icc_AddS |
| comm | Int.In_Icc_AddS.is.InSub |
| mp | Int.In_Icc_AddS.of.InSub |
| mpr | Int.InSub.of.In_Icc_AddS |
-/
@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [Preorder α]
  [AddLeftMono α] [AddRightMono α]
-- given
  (x a b d : α) :
-- imply
  x - d ∈ Icc a b ↔ x ∈ Icc (a + d) (b + d) := by
-- proof
  constructor
  · intro h
    have h := InAdd.of.In_Icc d h
    simpa [EqAddSub] using h
  · intro h
    have h := InSub.of.In_Icc d h
    simpa [EqSubAdd] using h


@[main, comm, mp, mpr]
private lemma left
  [AddCommGroup α]
  [Preorder α]
  [AddLeftMono α] [AddRightMono α]
-- given
  (x a b d : α) :
-- imply
  x - d ∈ Icc a b ↔ x ∈ Icc (d + a) (d + b) := by
-- proof
  rw [main, add_comm d a, add_comm d b]


-- created on 2026-08-08
