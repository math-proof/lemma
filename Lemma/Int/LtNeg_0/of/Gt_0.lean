import Lemma.Int.LtSubS.is.Lt
import Lemma.Nat.Sub.eq.Zero
import Lemma.Int.Sub0.eq.Neg
open Int Nat


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {a : α}
-- given
  (h : a > 0) :
-- imply
  -a < 0 := by
-- proof
  have h := GtSubS.of.Gt a h
  simp only [Sub.eq.Zero, Sub0.eq.Neg] at h
  exact h


-- created on 2024-11-29
