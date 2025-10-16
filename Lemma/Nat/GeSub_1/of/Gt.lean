import Lemma.Nat.Le_Sub_1.of.Lt
open Nat


@[main]
private lemma main
  [IntegerRing α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a - 1 ≥ b :=
-- proof
  Le_Sub_1.of.Lt h


-- created on 2024-07-01
-- updated on 2025-06-02
