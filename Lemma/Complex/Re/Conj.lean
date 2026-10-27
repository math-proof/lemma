import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {z : ℂ} :
-- imply
  re z = re (~z) :=
-- proof
  (Complex.conj_re z).symm


-- created on 2023-06-24
