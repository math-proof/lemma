import Lemma.Int.EqAddSub
import Lemma.Int.EqSubAdd
import Lemma.Int.In_Ico.is.InAdd
import Lemma.Int.In_Ico.is.InSub
open Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.InSub.is.In_Ico_AddS |
| comm | Int.In_Ico_AddS.is.InSub |
| mp | Int.In_Ico_AddS.of.InSub |
| mpr | Int.InSub.of.In_Ico_AddS |
-/
@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [Preorder α]
  [AddLeftMono α] [AddRightMono α]
  [AddLeftStrictMono α] [AddRightStrictMono α]
-- given
  (x a b d : α) :
-- imply
  x - d ∈ Ico a b ↔ x ∈ Ico (a + d) (b + d) := by
-- proof
  constructor
  · intro h
    have h := InAdd.of.In_Ico d h
    simpa [EqAddSub] using h
  · intro h
    have h := InSub.of.In_Ico d h
    simpa [EqSubAdd] using h


@[main, comm, mp, mpr]
private lemma left
  [AddCommGroup α]
  [Preorder α]
  [AddLeftMono α] [AddRightMono α]
  [AddLeftStrictMono α] [AddRightStrictMono α]
-- given
  (x a b d : α) :
-- imply
  x - d ∈ Ico a b ↔ x ∈ Ico (d + a) (d + b) := by
-- proof
  rw [main, add_comm d a, add_comm d b]


-- created on 2026-08-08
