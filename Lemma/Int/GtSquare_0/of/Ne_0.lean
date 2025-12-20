import Lemma.Int.GeSquare_0
import Lemma.Int.Eq_0.is.EqSquare_0
import Lemma.Nat.Gt.is.Ge.Ne
open Int Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a² > 0 :=
-- proof
  Gt.of.Ge.Ne
    (GeSquare_0 a)
    (NeSquare_0.of.Ne_0 h)


-- created on 2024-11-29
-- updated on 2025-03-30
