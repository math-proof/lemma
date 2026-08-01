import Lemma.Int.LeSub.is.Le_Add
import Lemma.Nat.Add
open Int Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LeSub.is.LeSub |
| mp | Int.LeSub.of.LeSub |
| mp.comm | Int.Ge_Sub.of.Ge_Sub |
| comm.is | Int.Ge_Sub.is.Ge_Sub |
-/
@[main, mp, mp.comm, comm.is]
private lemma main
  [AddCommGroup α]
  [LE α]
  [AddRightMono α]
-- given
  (a b c : α) :
-- imply
  a - b ≤ c ↔ a - c ≤ b := by
-- proof
  repeat rw [LeSub.is.Le_Add]
  rw [Add.comm]


-- created on 2025-12-08
