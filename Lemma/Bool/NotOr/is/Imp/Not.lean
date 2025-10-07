import Lemma.Bool.NotOr.is.AndNotS
import Lemma.Bool.Imp.is.OrNot
import Lemma.Bool.AndOr.is.OrAndS
open Bool


@[main, comm]
private lemma main
-- given
  (p q : Prop) :
-- imply
  ¬(p ∨ q) ↔ (q → p) ∧ ¬p := by
-- proof
  rw [NotOr.is.AndNotS]
  rw [Imp.is.OrNot]
  rw [AndOr.is.OrAndS]
  simp
  rw [And.comm]


-- created on 2025-04-09
