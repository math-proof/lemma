import Lemma.Bool.AndAnd.is.And_And
open Bool


@[main]
private lemma main
  {p q : Prop}
  (left : Bool := true) :
-- imply
  match left with
  | true =>
    (p ∧ q) ∧ ¬p ↔ False
  | false =>
    (q ∧ p) ∧ ¬p ↔ False := by
-- proof
  match left with
  | true =>
    rw [And.comm (b := q)]
    rw [AndAnd.is.And_And]
    simp
  | false =>
    rw [AndAnd.is.And_And]
    simp


-- created on 2024-07-01
