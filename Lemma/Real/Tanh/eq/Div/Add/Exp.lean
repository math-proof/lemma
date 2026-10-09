import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.tanh x = (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) := by
-- proof
  have hp : 0 < Real.exp x + Real.exp (-x) := by
    linarith [Real.exp_pos x, Real.exp_pos (-x)]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  field_simp [hp.ne']


-- created on 2023-11-26
