import Lemma.Bool.ImpAndS.of.Imp.Imp
open Bool


@[path]
private lemma main
-- given
  (h : p → q)
  (r : Prop) :
-- imply
  p ∧ r → q ∧ r := by
-- proof
  apply ImpAndS.of.Imp.Imp h
  simp


@[path]
private lemma left
-- given
  (h : p → q)
  (r : Prop) :
-- imply
  r ∧ p → r ∧ q := by
-- proof
  apply ImpAndS.of.Imp.Imp _ h
  simp


-- created on 2018-03-31
