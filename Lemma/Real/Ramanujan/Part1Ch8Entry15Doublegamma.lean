import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch8Entry15Doublegamma
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch8
open Entry15Doublegamma


/--
[ramanujan_part1_ch8_entry15_doublegamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry15Doublegamma.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry15_doublegamma_eq
  {n : ℂ} :
-- imply
  Tendsto chapter8Entry15A atTop atTop ∧
    IsBigO atTop
    (fun x : ℝ => chapter8Entry15Power n x - chapter8Entry15Approx n x)
    (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 8) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry15Doublegamma.ramanujan_part1_ch8_entry15_doublegamma n


-- created on 2026-10-20
