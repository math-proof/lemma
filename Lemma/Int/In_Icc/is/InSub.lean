import Lemma.Int.In_Icc.is.InAdd
import Lemma.Int.EqAddSub
open Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.In_Icc.is.InSub |
| comm | Int.InSub.is.In_Icc |
| mp | Int.InSub.of.In_Icc |
| mpr | Int.In_Icc.of.InSub |
| mp.mt | Int.NotIn_Icc.of.NotInSub |
| mpr.mt | Int.NotInSub.of.NotIn_Icc |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [AddGroup α]
  [Preorder α]
  [AddLeftMono α] [AddRightMono α]
-- given
  (x a b d : α) :
-- imply
  x ∈ Icc a b ↔ x - d ∈ Icc (a - d) (b - d) := by
-- proof
  constructor <;>
    intro h
  ·
    simp_all [Set.mem_Icc]
  ·
    have h := InAdd.of.In_Icc d h
    simp only [EqAddSub] at h
    assumption


-- created on 2018-04-12
