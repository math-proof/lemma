import Lemma.Bool.IffAndOr
open Bool


@[main]
private lemma main
  (left : Bool := false) :
-- imply
  match left with
  | true => p ∧ (p ∨ q) ↔ p
  | false => p ∧ (q ∨ p) ↔ p := by
-- proof
  rw [And.comm]
  rw [And.comm (a := p)]
  match left with
  | true =>
    apply IffAndOr false
  | false =>
    apply IffAndOr true


-- created on 2024-07-01
