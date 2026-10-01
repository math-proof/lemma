import Lemma.Bool.Cond.of.Gt_0
open Bool


@[main]
private lemma main
  [Decidable p]
-- given
  (h : Bool.toNat p ≠ 0) :
-- imply
  p :=
-- proof
  Cond.of.Gt_0 (Nat.pos_of_ne_zero h)


-- created on 2023-11-05
