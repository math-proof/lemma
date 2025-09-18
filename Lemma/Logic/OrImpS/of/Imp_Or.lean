import Lemma.Logic.Imp.is.OrNot
import Lemma.Logic.OrOr.is.Or_Or
import Lemma.Logic.Or_Or
open Logic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → (q ∨ r)) :
-- imply
  (p → q) ∨ (p → r) := by
-- proof
  rw [Imp.is.OrNot] at h
  rw [Imp.is.OrNot]
  rw [Imp.is.OrNot]
  rw [OrOr.is.Or_Or]
  rw [Or_Or.comm] at h
  apply Or.inr h


-- created on 2024-07-01
