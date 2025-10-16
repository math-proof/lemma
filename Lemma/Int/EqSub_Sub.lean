import Lemma.Int.AddSub.eq.Sub_Sub
import Lemma.Int.Sub.eq.Zero
import Lemma.Algebra.EqAdd0
open Algebra Int


@[main]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  a - (a - b) = b := by
-- proof
  rw [Sub_Sub.eq.AddSub]
  rw [Sub.eq.Zero]
  rw [EqAdd0]


-- created on 2025-04-06
