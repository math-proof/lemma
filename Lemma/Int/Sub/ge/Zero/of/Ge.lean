import Lemma.Nat.Sub.eq.Zero
import Lemma.Int.LeSubS.is.Le
open Int Nat


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  x - y ≥ 0 := by
-- proof
  have h := GeSubS.of.Ge y h
  rwa [Sub.eq.Zero] at h


-- created on 2025-03-15
-- updated on 2025-10-16
