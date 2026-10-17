import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import sympy.Basic
open MeasureTheory


@[path]
private lemma main
  {a b : ℝ}
  {n : ℕ} :
-- imply
  ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) :=
-- proof
  integral_pow n


-- created on 2026-10-11
-- updated on 2026-10-17
