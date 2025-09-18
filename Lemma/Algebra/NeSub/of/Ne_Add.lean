import Lemma.Algebra.Ne_Sub.of.NeAdd
open Algebra


@[main]
private lemma left
  [AddCommGroup α]
  {x a b : α}
-- given
  (h : a ≠ b + x) :
-- imply
  a - b ≠ x :=
-- proof
  (Ne_Sub.of.NeAdd.left h.symm).symm


@[main]
private lemma main
  [AddGroup α]
  {x a b : α}
-- given
  (h : a ≠ x + b) :
-- imply
  a - b ≠ x :=
-- proof
  (Ne_Sub.of.NeAdd h.symm).symm


-- created on 2024-11-27
-- updated on 2025-06-11
