import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch8Entry19Gaussdigamma
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum
open MathlibExt.Analysis.Ramanujan.Part1Ch8
open Entry19Gaussdigamma


/--
[ramanujan_part1_ch8_entry19_gaussdigamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry19Gaussdigamma.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry19_gaussdigamma_eq
  {n : ℕ} :
-- imply
  (∀ m ≤ n,
    Tendsto (chapter8LogPowerConstantApprox m) atTop
    (𝓝 (chapter8LogPowerConstant m))) ∧
    IsBigO atTop
    (fun x : ℕ =>
    chapter8Entry19Combination n x - chapter8Entry19Approx n x)
    (fun x : ℕ => 1 / (x : ℝ) ^ (n + 3)) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry19Gaussdigamma.ramanujan_part1_ch8_entry19_gaussdigamma n


-- created on 2026-10-20
