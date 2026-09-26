import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.Basic
open Real


@[main]
private lemma main
  {ν : ℝ}
  {n₀ : ℕ}
-- given
  (h₀ : 1 / 2 < ν) :
-- imply
  Summable fun n : ℕ => (((n : ℝ) + n₀) ^ (-ν)) ^ 2 := by
-- proof
  have hs : Summable fun n : ℕ => ((n : ℝ)) ^ (-(2 * ν)) := summable_nat_rpow.2 (by linarith)
  refine ((summable_nat_add_iff n₀).2 hs).congr fun n => ?_
  rw [← rpow_natCast, ← rpow_mul (by positivity)]
  push_cast
  ring_nf


-- created on 2026-09-26