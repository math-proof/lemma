import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry16Kummercongruence
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry16Kummercongruence


/--
[ramanujan_part1_ch7_entry16_kummercongruence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry16Kummercongruence.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry16_kummercongruence_eq
  {r : ℂ}
  {x : ℝ}
-- given
  (hr : -1 < r.re)
  (hx0 : 0 < x)
  (hx1 : x < 1) :
-- imply
  ∃! L : ℂ,
    Tendsto (chapter7Entry16PartialSum r x) atTop (𝓝 L) ∧
    chapter7Entry16Left r x hx0 hx1 =
    Complex.sin ((Real.pi : ℂ) * r / 2) * L := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry16Kummercongruence.ramanujan_part1_ch7_entry16_kummercongruence r x hr hx0 hx1


-- created on 2026-10-20
