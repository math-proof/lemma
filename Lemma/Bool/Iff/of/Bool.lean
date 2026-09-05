import Lemma.Bool.Imp.of.Bool
open Bool


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (h : Bool.toNat p = Bool.toNat q) :
-- imply
  p ↔ q := by
-- proof
  constructor
  ·
    apply Imp.of.Bool h
  ·
    apply Imp.of.Bool h.symm


-- created on 2018-03-22
