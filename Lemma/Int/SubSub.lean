import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Nat.Add
open Int Nat


@[main]
private lemma Comm
  [SubtractionCommMonoid α]
  {a b c : α} :
-- imply
  a - b - c = a - c - b := by
-- proof
  repeat rw [SubSub.eq.Sub_Add]
  rw [Add.comm]


-- created on 2025-06-06
-- updated on 2025-10-12
