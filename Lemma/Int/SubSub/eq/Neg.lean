import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Nat.Add
import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Nat.Sub.eq.Zero
open Nat Int


@[main]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  a - b - a = -b := by
-- proof
  rw [SubSub.eq.Sub_Add]
  rw [Add.comm]
  rw [Sub_Add.eq.SubSub]
  rw [Sub.eq.Zero]
  simp


-- created on 2025-03-30
