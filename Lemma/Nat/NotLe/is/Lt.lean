import Lemma.Nat.NotLe.is.Gt
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  ¬(a ≤ b) ↔ b < a :=
-- proof
  -- NotLe.is.Gt
  not_le


-- created on 2025-03-29
-- updated on 2025-03-30
