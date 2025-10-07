import Lemma.Bool.AndAndNot.is.False
open Bool


@[main]
private lemma main :
-- imply
  (q ∧ ¬p) ∧ p ↔ False := by
-- proof
  rw [And.comm (a := q)]
  apply AndAndNot.is.False


-- created on 2024-07-01
