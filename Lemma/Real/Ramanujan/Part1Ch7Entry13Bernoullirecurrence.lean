import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry13Bernoullirecurrence
open scoped Nat Real BigOperators Interval ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry13Bernoullipolyadd (chapter7StieltjesApprox)
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry13Bernoullirecurrence


/--
[ramanujan_part1_ch7_entry13_bernoullirecurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry13Bernoullirecurrence.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry13_bernoullirecurrence_eq
  {c : ℕ → ℝ}
-- given
  (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) :
-- imply
  ∀ s : ℂ, s ≠ 1 →
    HasSum (chapter7StieltjesLaurentTerm c s)
    (riemannZeta s - 1 / (s - 1)) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry13Bernoullirecurrence.ramanujan_part1_ch7_entry13_bernoullirecurrence c hc


-- created on 2026-10-20
