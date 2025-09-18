import Lemma.Algebra.Le_Sub.is.LeAdd
open Algebra


@[main]
private lemma main
  [AddGroup α]
  [LE α]
  [AddRightMono α]
  {a b c : α}
-- given
  (h : a - b ≥ c) :
-- imply
  a ≥ c + b :=
-- proof
  LeAdd.of.Le_Sub h


@[main]
private lemma left
  [AddCommGroup α]
  [LE α]
  [AddLeftMono α]
  {a b c : α}
-- given
  (h : a - c ≥ b) :
-- imply
  a ≥ c + b :=
-- proof
  LeAdd.of.Le_Sub.left h


-- created on 2024-11-27
-- updated on 2025-06-21
