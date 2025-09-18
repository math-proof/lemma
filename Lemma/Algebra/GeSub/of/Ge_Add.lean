import Lemma.Algebra.Le_Sub.of.LeAdd
import Lemma.Algebra.Le_Sub.is.LeAdd
open Algebra


@[main]
private lemma nat
  {a b c : ℕ}
-- given
  (h : c ≥ a + b) :
-- imply
  c - b ≥ a :=
-- proof
  Le_Sub.of.LeAdd.nat h


@[main]
private lemma left.nat
  {a b c : ℕ}
-- given
  (h : c ≥ a + b) :
-- imply
  c - a ≥ b :=
-- proof
  Le_Sub.of.LeAdd.left.nat h


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


-- created on 2024-11-27
