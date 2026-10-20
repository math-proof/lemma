import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry14Bernoulliasymptotic


/--
[ramanujan_part1_ch7_entry14_bernoulliasymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry14Bernoulliasymptotic.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry14_bernoulliasymptotic_eq
  {c : ℕ → ℝ}
-- given
  (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) :
-- imply
  Summable (chapter7Entry14Cor2LeftTerm 1) ∧
    Summable (chapter7Entry14Cor2ConstantTerm c) ∧
    ∀ s : ℝ, 0 < s →
    Summable (chapter7Entry14Cor2LeftTerm s) ∧
    Summable (chapter7Entry14Cor2PowerTerm c s) ∧
    (∑' j : ℕ, chapter7Entry14Cor2LeftTerm s j) =
    -Real.log s + chapter7Entry14Cor2Constant c +
    (1 - Real.eulerMascheroniConstant) * s -
    ∑' j : ℕ, chapter7Entry14Cor2PowerTerm c s j := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry14Bernoulliasymptotic.ramanujan_part1_ch7_entry14_bernoulliasymptotic c hc


-- created on 2026-10-20
