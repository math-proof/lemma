import Lemma.Int.LtSubS.is.Lt
import Lemma.Nat.Sub.eq.Zero
open Nat Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x - y < 0 := by
-- proof
  have h := LtSubS.of.Lt y h
  rwa [Sub.eq.Zero] at h


-- created on 2025-03-15
-- updated on 2025-04-04
