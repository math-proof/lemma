import Lemma.Bool.AndAnd__Not.is.False
import Lemma.Bool.Iff_Not.of.Iff_Not
import Lemma.Bool.Imp.of.Cond
open Bool


@[main]
private lemma main :
-- imply
  (¬p ∧ q) ∧ p ↔ False := by
-- proof
  let p' := ¬p
  have h := Iff_Not.of.Iff_Not (by rfl : p' ↔ ¬p)
  rw [h]
  simp
  apply Imp.of.Cond


-- created on 2024-07-01
