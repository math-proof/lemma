import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic
import Notation.Algebra.Power
open Complex


@[path]
private lemma main
  {z : ℂ} :
-- imply
  Real.cos (arg z) =
    if z = 0 then
      1
    else
      re z / √((re z)² + (im z)²) := by
-- proof
  rw [← Complex.norm_eq_sqrt_sq_add_sq]
  split_ifs with h
  ·
    rw [h, arg_zero, Real.cos_zero]
  ·
    exact cos_arg h


-- created on 2018-06-12
-- updated on 2026-11-22
