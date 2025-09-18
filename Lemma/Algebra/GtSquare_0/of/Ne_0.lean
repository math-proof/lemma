import Lemma.Algebra.GeSquare_0
import Lemma.Algebra.NeSquare_0.of.Ne_0
import Lemma.Algebra.Gt.is.Ge.Ne
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a² > 0 :=
-- proof
  Gt.of.Ge.Ne
    (GeSquare_0 (a := a))
    (NeSquare_0.of.Ne_0 h)


-- created on 2024-11-29
-- updated on 2025-03-30
