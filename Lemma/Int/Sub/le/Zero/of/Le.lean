import Lemma.Int.Sub.eq.Zero
import Lemma.Int.LeSubS.is.Le
open Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  x - y ≤ 0 := by
-- proof
  have := LeSubS.of.Le y h
  rwa [Sub.eq.Zero] at this


-- created on 2025-03-15
