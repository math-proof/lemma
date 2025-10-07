import Lemma.Bool.Imp.is.OrNot
import Lemma.Bool.OrOr.is.Or_Or
import Lemma.Bool.Or_Or
open Bool


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → (q ∨ r)) :
-- imply
  (p → q) ∨ (p → r) := by
-- proof
  rw [Imp.is.OrNot] at h
  repeat rw [Imp.is.OrNot]
  rw [OrOr.is.Or_Or]
  rw [Or_Or.comm] at h
  apply Or.inr h


-- created on 2024-07-01
