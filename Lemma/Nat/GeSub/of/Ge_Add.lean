import Lemma.Nat.Le_Sub.of.LeAdd
open Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : c ≥ a + b) :
-- imply
  c - b ≥ a :=
-- proof
  Le_Sub.of.LeAdd h


@[main]
private lemma left
  {a b c : ℕ}
-- given
  (h : c ≥ a + b) :
-- imply
  c - a ≥ b :=
-- proof
  Le_Sub.of.LeAdd.left h


-- created on 2024-11-27
-- updated on 2025-10-16
