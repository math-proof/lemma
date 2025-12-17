import Lemma.Set.In_Icc.is.InAdd
import Lemma.Int.EqAddSub
open Set Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Icc.is.InSub |
| comm | Set.InSub.is.In_Icc |
| mp | Set.InSub.of.In_Icc |
| mpr | Set.In_Icc.of.InSub |
| mp.mt | Set.NotIn_Icc.of.NotInSub |
| mpr.mt | Set.NotInSub.of.NotIn_Icc |
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


-- created on 2025-05-12
