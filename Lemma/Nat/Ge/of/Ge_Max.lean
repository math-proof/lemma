import Lemma.Algebra.GeMax
import Lemma.Nat.Ge.of.Ge.Ge
open Algebra Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : x ≥ a ⊔ b) :
-- imply
  x ≥ b := by
-- proof
  have h_ge := GeMax a b
  apply Ge.of.Ge.Ge h h_ge


-- created on 2025-05-31
