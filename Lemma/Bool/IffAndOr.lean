import Lemma.Bool.AndOr.is.OrAndS
open Bool


@[main]
private lemma main
  (right : Bool := true) :
-- imply
  match right with
  | true => (q ∨ p) ∧ p ↔ p
  | false => (p ∨ q) ∧ p ↔ p := by
-- proof
  simp [AndOr.is.OrAndS]
  cases right <;> simp


-- created on 2024-07-01
