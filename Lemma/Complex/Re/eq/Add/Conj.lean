import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {z : ℂ} :
-- imply
  (re z : ℂ) = (z + ~z) / 2 := by
-- proof
  rw [Complex.add_conj]
  push_cast
  ring


-- created on 2023-06-24
