import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch7Entry13Bernoullipolyadd

open Ramanujan.Part1Ch7.Entry13Bernoullipolyadd

/--
[Part1Ch7Entry13Bernoullipolyadd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry13Bernoullipolyadd.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry13_bernoullipolyadd_is :
-- imply
  ∃! c : ℕ → ℝ,
    (∀ k : ℕ, Filter.Tendsto (chapter7StieltjesApprox k) Filter.atTop (nhds (c k))) ∧
      c 0 = Real.eulerMascheroniConstant := by
-- proof
  apply Ramanujan.Part1Ch7.Entry13Bernoullipolyadd.ramanujan_part1_ch7_entry13_bernoullipolyadd

-- created on 2026-10-10
