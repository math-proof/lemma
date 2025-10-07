import Lemma.Bool.Imp.of.EqBoolS
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
    apply Imp.of.EqBoolS h
  ·
    apply Imp.of.EqBoolS (h.symm)


-- created on 2025-04-20
