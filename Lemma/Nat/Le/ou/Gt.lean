import Lemma.Bool.OrOr.is.Or_Or
import Lemma.Nat.Le.is.Lt.ou.Eq
import Lemma.Nat.Lt.ou.Eq.ou.Gt
open Bool Nat


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ≤ b ∨ a > b := by
-- proof
  rw [Le.is.Lt.ou.Eq]
  rw [OrOr.is.Or_Or]
  apply Lt.ou.Eq.ou.Gt


-- created on 2026-07-19
