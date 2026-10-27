import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℂ} :
-- imply
  ‖x + ~y‖ = ‖~(x + ~y)‖ :=
-- proof
  (Complex.norm_conj _).symm


-- created on 2023-06-24
