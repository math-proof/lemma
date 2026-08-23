import sympy.Basic


@[main]
private lemma main
  [Decidable p]
-- given
  (a b : ℝ) :
-- imply
  Real.sin (if p then
    a
  else
    b) = if p then
    Real.sin a
  else
    Real.sin b := by
-- proof
  split_ifs <;> rfl


-- created on 2022-01-20
-- updated on 2026-08-23
