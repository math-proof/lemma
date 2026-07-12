import Lemma.Nat.Ne0'1
open Nat


@[main]
private lemma main
  [Zero α]
  [One α]
  [NeZero (1 : α)]
  {a : α}
-- given
  (h : a = 0) :
-- imply
  a ≠ 1 :=
-- proof
  h.symm.subst (motive := fun a => a ≠ 1) Ne0'1


-- created on 2025-04-20
