import Lemma.Int.LeSub.is.Le_Add
import Lemma.Nat.Add
open Int Nat


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
