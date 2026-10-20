import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry1Powersum
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry1Powersum


/--
[ramanujan_part1_ch7_entry1_powersum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry1Powersum.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry1_powersum_eq
  {r : ℂ}
  {N : ℕ}
-- given
  (hr : r ≠ -1)
  (hN : 0 < N)
  (hu : r.re < 2 * N) :
-- imply
  IsBigO atTop
    (fun n : ℕ => chapter7PowerSum r n - chapter7Entry1Approx r N n)
    (fun n : ℕ => Real.rpow (n : ℝ) (r.re - 2 * (N : ℝ))) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum.ramanujan_part1_ch7_entry1_powersum r N hr hN hu


-- created on 2026-10-20
