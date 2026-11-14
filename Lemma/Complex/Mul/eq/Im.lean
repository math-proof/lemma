import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic
open Complex


@[path]
private lemma main
  {c : ℝ}
  {z : ℂ} :
-- imply
  im z * c = im (z * c) := by
-- proof
  simp


-- created on 2023-06-03
