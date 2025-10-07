import Lemma.Logic.NotOr.is.AndNotS
import Lemma.Bool.Imp.is.Or_Not
import Lemma.Logic.Imp.is.OrNot
import Lemma.Logic.ImpOr.is.Imp.Imp
open Logic Bool


@[main]
private lemma main
  {p q : Prop} :
-- imply
  p ∧ q ∨ ¬p ∧ ¬q ↔ (¬p ∨ q) ∧ (p ∨ ¬q) := by
-- proof
  rw [AndNotS.is.NotOr]
  rw [Or_Not.is.Imp]
  rw [Or_Not.is.Imp]
  rw [OrNot.is.Imp]
  rw [ImpOr.is.Imp.Imp]
  tauto


-- created on 2025-04-18
