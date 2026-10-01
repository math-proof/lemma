import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h : a > 0) :
-- imply
  a * x + b < 0 ↔ x < -b / a := by
-- proof
  rw [lt_div_iff₀ h]
  constructor
  ·
    intro h'
    linarith
  ·
    intro h'
    linarith


-- created on 2023-04-11
