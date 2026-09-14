import sympy.Basic
import sympy.integrals.integrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory


@[main]
private lemma main
  {f g : ℝ → ℝ}
-- given
  (h : ∀ x : ℝ, f x = g x) :
-- imply
  ∫ x : ℝ, f x = ∫ x : ℝ, g x :=
-- proof
  integral_congr_ae (ae_of_all volume h)


-- created on 2020-05-17
