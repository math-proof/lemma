import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch8Entry10Qgammalimit
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch8
open Entry10Qgammalimit


/--
[ramanujan_part1_ch8_entry10_qgammalimit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry10Qgammalimit.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry10_qgammalimit_eq
  {x : ℂ}
-- given
  (hx : x.re < 0) :
-- imply
  x ≠ 0 ∧
    Complex.Gamma (1 - 1 / x) ≠ 0 ∧
    chapter8Entry10Kernel x 0 = 0 ∧
    chapter8Entry10Kernel x 1 = -1 / x ∧
    (∀ u : ℝ, u ∈ Set.Ioo 0 1 →
    (u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1) ≠ 0 ∧
    chapter8Entry10Kernel x u =
    ((1 - u : ℝ) : ℂ) /
    ((u : ℂ) * (Entry9Qgamma.chapter8UnitPow x u - 1))) ∧
    IntervalIntegrable (chapter8Entry10Kernel x) volume 0 1 ∧
    Complex.digamma (1 - 1 / x) +
    (Real.eulerMascheroniConstant : ℂ) =
    -x * ∫ u in (0 : ℝ)..1, chapter8Entry10Kernel x u := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry10Qgammalimit.ramanujan_part1_ch8_entry10_qgammalimit x hx


-- created on 2026-10-20
