import Lemma.Real.GtExp_0
import Lemma.Nat.Ge.of.Gt
open Real Nat


@[main]
private lemma main
  [ExpPos α]
-- given
  (x : α) :
-- imply
  exp x ≥ 0 :=
-- proof
  Ge.of.Gt (GtExp_0 x)


-- created on 2025-10-05
