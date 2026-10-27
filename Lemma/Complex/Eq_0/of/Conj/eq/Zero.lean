import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℂ}
-- given
  (h : ~x = 0) :
-- imply
  x = 0 :=
-- proof
  (map_eq_zero (starRingEnd ℂ)).mp h


-- created on 2023-05-02
