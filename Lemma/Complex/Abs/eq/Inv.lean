import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℂ} :
-- imply
  ‖x⁻¹‖ = ‖x‖⁻¹ := by
-- proof
  exact norm_inv x


-- created on 2018-07-26
