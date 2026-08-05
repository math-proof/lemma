import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Int.Abs.eq.Neg.of.Lt_0
open Int Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x ≤ 0) :
-- imply
  |x| = -x := by
-- proof
  if h_0 : x = 0 then
    subst h_0
    simp_all
  else
    apply Abs.eq.Neg.of.Lt_0
    apply Lt.of.Le.Ne h h_0


-- created on 2025-12-21
