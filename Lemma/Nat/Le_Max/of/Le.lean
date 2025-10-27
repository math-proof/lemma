import Lemma.Nat.GeMax
import Lemma.Nat.Le.of.Le.Le
open Nat


@[main]
private lemma main
  [LinearOrder α]
-- given
  (h : c ≤ a)
  (b : α) :
-- imply
  c ≤ a ⊔ b := by
-- proof
  have := GeMax.left a b
  apply Le.of.Le.Le h this


-- created on 2025-05-14
