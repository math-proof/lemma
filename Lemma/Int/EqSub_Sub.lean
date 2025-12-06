import Lemma.Int.AddSub.eq.Sub_Sub
import Lemma.Nat.Sub.eq.Zero
import Lemma.Nat.EqAdd0
open Int Nat


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
