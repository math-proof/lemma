import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {z : ℂ} :
-- imply
  sign z =
    if z = 0 then
      0
    else
      z / ‖z‖ := by
-- proof
  unfold Complex.sign
  split_ifs with h
  ·
    subst h
    simp
  ·
    rfl


-- created on 2023-05-25
