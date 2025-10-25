import Lemma.Nat.Le_Sub.of.LeAdd
import Lemma.Int.Le_Sub.is.LeAdd
open Nat Int


@[main]
private lemma left
  [AddCommGroup α] [LE α] [AddLeftMono α]
  {a b c : α}
-- given
  (h : c ≥ a + b) :
-- imply
  c - a ≥ b :=
-- proof
  Le_Sub.of.LeAdd.left h


@[main]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
  {a b c : α}
-- given
  (h : c ≥ a + b) :
-- imply
  c - b ≥ a :=
-- proof
  Le_Sub.of.LeAdd h


-- created on 2025-10-16
