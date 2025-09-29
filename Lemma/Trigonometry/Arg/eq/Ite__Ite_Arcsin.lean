import sympy.functions.elementary.trigonometric
import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {z : ℂ} :
-- imply
  arg z =
    if re z ≥ 0 then
      arcsin (im z / ‖z‖)
    else if im z ≥ 0 then
      arcsin (im (-z) / ‖z‖) + π
    else
      arcsin (im (-z) / ‖z‖) - π := by
-- proof
  rw [arg]


-- created on 2025-01-06
