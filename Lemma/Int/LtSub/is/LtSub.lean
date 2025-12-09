import Lemma.Int.LtSub.is.Lt_Add
import Lemma.Nat.Add
open Int Nat


@[main, mp, mp.comm, comm.is]
private lemma main
  [AddCommGroup α]
  [LT α]
  [AddRightStrictMono α]
-- given
  (a b c : α) :
-- imply
  a - b < c ↔ a - c < b := by
-- proof
  simp [LtSub.is.Lt_Add]
  rw [Add.comm]


-- created on 2025-12-08
