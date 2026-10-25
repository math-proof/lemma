import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_11_10
open Chapter11.BoundedInterval Chapter9 Chapter10
open Chapter11 hiding RS_integ
open Chapter11.PiecewiseConstantOn


/--
[PiecewiseConstantOn.RS_integ_eq_integ_of_mul_deriv](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_10.lean)
-/
@[path]
private lemma main
  {a b:ℝ}
  {α f:ℝ → ℝ}
-- given
  (hα_diff: DifferentiableOn ℝ α (Icc a b))
  (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: PiecewiseConstantOn f (Icc a b)) :
-- imply
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
    Chapter11.integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α :=
-- proof
  Chapter11.PiecewiseConstantOn.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα' hf


-- created on 2026-10-22
