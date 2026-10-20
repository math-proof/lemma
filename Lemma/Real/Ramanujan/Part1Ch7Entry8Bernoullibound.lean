import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry8Bernoullibound
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry8Bernoullibound


/--
[ramanujan_part1_ch7_entry8_bernoullibound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry8Bernoullibound.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry8_bernoullibound_eq
  {r : ℕ}
  {x : ℂ}
-- given
  (hr : 0 < r) :
-- imply
  chapter7IntegerPhi r x = chapter7Entry8BernoulliForm r x ∧
    chapter7IntegerPhi r x = chapter7Entry8ZetaForm r x ∧
    ∀ n : ℕ,
    chapter7IntegerPhi r n = ∑ k ∈ Icc 1 n, (k : ℂ) ^ r := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8Bernoullibound.ramanujan_part1_ch7_entry8_bernoullibound r hr x

/--
[chapter7Phi_eq_chapter7IntegerPhi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry8Bernoullibound.lean)
-/
@[path]
private lemma chapter7Phi_eq_chapter7IntegerPhi_eq
  {r : ℕ}
  {x : Chapter7PhiArgument}
-- given
  (hr : r ≠ 0) :
-- imply
  chapter7Phi r x = chapter7IntegerPhi r (x : ℝ) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8Bernoullibound.chapter7Phi_eq_chapter7IntegerPhi r hr x

/--
[ramanujan_part1_ch7_entry8_phi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry8Bernoullibound.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry8_phi_eq
  {r : ℕ}
  {x : Chapter7PhiArgument}
-- given
  (hr : 0 < r) :
-- imply
  chapter7Phi r x = chapter7Entry8BernoulliForm r (x : ℝ) ∧
    chapter7Phi r x = chapter7Entry8ZetaForm r (x : ℝ) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry8Bernoullibound.ramanujan_part1_ch7_entry8_phi r hr x


-- created on 2026-10-20
