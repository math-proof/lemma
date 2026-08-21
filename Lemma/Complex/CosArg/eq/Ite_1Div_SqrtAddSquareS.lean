import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import Lemma.Complex.Norm.eq.Sqrt
open Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  Real.cos (arg z) =
    if z = 0 then
      1
    else
      re z / √((re z)² + (im z)²) := by
-- proof
  rw [← Norm.eq.Sqrt (z := z)]
  split_ifs with h
  ·
    rw [h, arg_zero, Real.cos_zero]
  ·
    exact Complex.cos_arg h


-- created on 2018-06-12
-- updated on 2026-08-21
