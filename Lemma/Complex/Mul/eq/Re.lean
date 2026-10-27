import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {c : ℝ}
  {z : ℂ} :
-- imply
  re z * c = re (z * c) := by
-- proof
  simp


-- created on 2023-06-03
