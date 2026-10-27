import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℂ} :
-- imply
  ‖x⁻¹‖ = ‖x‖⁻¹ := by
-- proof
  exact norm_inv x


-- created on 2018-07-26
