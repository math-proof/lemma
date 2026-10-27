import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  {a b : ℝ}
  {n : ℕ} :
-- imply
  ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) :=
-- proof
  integral_pow n


-- created on 2020-06-12
-- updated on 2026-10-26
