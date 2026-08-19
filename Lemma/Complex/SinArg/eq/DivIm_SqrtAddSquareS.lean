import sympy.functions.elementary.trigonometric
import Lemma.Complex.Norm.eq.Sqrt


@[main]
private lemma main
  {z : ℂ} :
-- imply
  sin (arg z) = im z / √((re z)² + (im z)²) := by
-- proof
  rw [← Complex.Norm.eq.Sqrt (z := z)]
  exact Complex.sin_arg z


-- created on 2018-07-25
-- updated on 2026-08-18
