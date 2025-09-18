import Lemma.Algebra.GeMax
import Lemma.Algebra.Gt.of.Gt.Ge
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : x > a ⊔ b) :
-- imply
  x > b := by
-- proof
  have h_ge := GeMax a b
  apply Gt.of.Gt.Ge h h_ge


-- created on 2025-05-31
