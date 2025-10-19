import Lemma.Algebra.AddSub.eq.SubAdd
import Lemma.Int.SubAdd.eq.Add_Sub
open Algebra Int


@[main]
private lemma main
  [AddCommGroup α]
  {a b c : α} :
-- imply
  a - b + c = a + (c - b) := by
-- proof
  rw [AddSub.eq.SubAdd]
  rw [SubAdd.eq.Add_Sub]


-- created on 2025-03-04
