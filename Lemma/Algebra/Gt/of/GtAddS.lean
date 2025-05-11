import Lemma.Algebra.Lt.of.LtAddS
open Algebra


@[main]
private lemma left
  [Add α]
  [LT α]
  [AddLeftReflectLT α]
  {a b d : α}
-- given
  (h : d + a > d + b) :
-- imply
  a > b :=
-- proof
  Lt.of.LtAddS.left h


@[main]
private lemma main
  [Add α]
  [LT α]
  [AddRightReflectLT α]
  {a b d : α}
-- given
  (h : a + d > b + d) :
-- imply
  a > b :=
-- proof
  Lt.of.LtAddS h


-- created on 2025-05-10
