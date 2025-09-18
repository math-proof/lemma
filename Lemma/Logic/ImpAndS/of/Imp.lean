import Lemma.Logic.ImpAndS.of.Imp.Imp
open Logic


@[main]
private lemma main
-- given
  (h : p → q)
  (r : Prop) :
-- imply
  p ∧ r → q ∧ r := by
-- proof
  apply ImpAndS.of.Imp.Imp h
  simp


@[main]
private lemma left
-- given
  (h : p → q)
  (r : Prop) :
-- imply
  r ∧ p → r ∧ q := by
-- proof
  apply ImpAndS.of.Imp.Imp _ h
  simp


-- created on 2025-07-20
