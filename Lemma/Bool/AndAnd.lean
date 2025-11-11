import Lemma.Bool.AndAnd.is.And_And
open Bool


@[main]
private lemma comm' :
-- imply
  (p ∧ q) ∧ r ↔ (p ∧ r) ∧ q := by
-- proof
  rw [AndAnd.is.And_And]
  rw [AndAnd.is.And_And]
  rw [And.comm (a := q)]


-- created on 2025-06-06
