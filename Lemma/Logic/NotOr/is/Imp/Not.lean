import Lemma.Logic.NotOr.is.AndNotS
import Lemma.Logic.Imp.is.OrNot
import Lemma.Logic.AndOr.is.OrAndS
open Logic


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
