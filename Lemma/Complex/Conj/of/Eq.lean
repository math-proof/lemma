import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℂ}
-- given
  (h : x = y) :
-- imply
  ~x = ~y := by
-- proof
  rw [h]


-- created on 2018-08-18
-- updated on 2026-10-26
