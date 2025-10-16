import Lemma.Int.Sub.eq.Zero
import Lemma.Int.GeSubS.of.Ge
open Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  x - y ≥ 0 := by
-- proof
  have := GeSubS.of.Ge h y
  rwa [Sub.eq.Zero] at this


-- created on 2025-03-15
-- updated on 2025-10-16
