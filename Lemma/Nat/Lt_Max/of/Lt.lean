import Lemma.Nat.GeMax
import Lemma.Nat.Lt.of.Lt.Le
open Nat


@[main]
private lemma main
  [LinearOrder α]
-- given
  (h : c < a)
  (b : α) :
-- imply
  c < a ⊔ b := by
-- proof
  have := GeMax.left a b
  apply Lt.of.Lt.Le h this


-- created on 2025-05-14
