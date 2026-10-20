import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry9Bernoulligrowth
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry9Bernoulligrowth


/--
[ramanujan_part1_ch7_entry9_bernoulligrowth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry9Bernoulligrowth.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry9_bernoulligrowth_eq
  {x : ℂ}
-- given
  (hx : chapter7Admissible x) :
-- imply
  (∀ r : ℂ, r.re < 0 → Summable (chapter7PowerDifferenceTerm r x)) ∧
    DifferentiableOn ℂ (fun r : ℂ => chapter7PowerDifferenceSum r x)
    {r : ℂ | r.re < 0} := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry9Bernoulligrowth.ramanujan_part1_ch7_entry9_bernoulligrowth x hx


-- created on 2026-10-20
