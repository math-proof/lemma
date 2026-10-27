import Mathlib.Analysis.Complex.Trigonometric
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  (x : ℝ) :
-- imply
  (Real.cos x : ℂ) = (Complex.exp (Complex.I * x) + Complex.exp (-Complex.I * x)) / 2 := by
-- proof
  rw [Complex.ofReal_cos, Complex.cos]
  ring_nf


-- created on 2018-06-14
-- updated on 2026-10-26
