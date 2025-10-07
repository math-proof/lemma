import Lemma.Logic.AndAnd__Not.is.False
import Lemma.Logic.Iff_Not.of.Iff_Not
import Lemma.Logic.Imp.of.Cond
open Logic


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
