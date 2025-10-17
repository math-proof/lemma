import Lemma.Nat.EqSubS.of.Eq
import Lemma.Int.EqSubAdd
open Int Nat


@[main]
private lemma main
  [AddGroup α]
  {x y : α}
-- given
  (h : x ≠ y)
  (d : α)
  (left : Bool := false) :
-- imply
  match left with
  | true => d + x ≠ d + y
  | false => x + d ≠ y + d := by
-- proof
  match left with
  | true =>
    intro h'
    have h' := EqSubS.of.Eq h' d
    simp at h'
    exact h h'
  | false =>
    intro h'
    have h' := EqSubS.of.Eq h' d
    simp only [EqSubAdd] at h'
    exact h h'


-- created on 2024-11-27
