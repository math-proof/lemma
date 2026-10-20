import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch6Entry2Stirlingseries
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch6
open Entry2Stirlingseries


/--
[ramanujan_part1_ch6_entry2_stirlingseries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry2Stirlingseries.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry2_stirlingseries_eq
  {z : ℂ}
-- given
  (hz : ∀ k : ℕ, z ≠ -((k + 1 : ℕ) : ℂ)) :
-- imply
  DifferentiableAt ℂ chapter6HarmonicInterpolation z ∧
    HasSum (fun k : ℕ => 1 / (z + (k + 1 : ℕ)) ^ 2)
    (deriv chapter6HarmonicInterpolation z) ∧
    Summable (fun k : ℕ => ‖(1 / (z + (k + 1 : ℕ)) ^ 2 : ℂ)‖) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch6.Entry2Stirlingseries.ramanujan_part1_ch6_entry2_stirlingseries z hz


-- created on 2026-10-20
