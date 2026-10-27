import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {z w : ℂ} :
-- imply
  re (z + w) = re z + re w :=
-- proof
  Complex.add_re z w


-- created on 2023-06-03
