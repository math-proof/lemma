import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic
open Complex


@[path]
private lemma main
  {x : ℂ} :
-- imply
  x + ~x = 2 * re x := by
-- proof
  rw [Complex.add_conj]
  push_cast
  ring


-- created on 2023-05-25
