import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry15Vonstaudtclausen
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry15Vonstaudtclausen


/--
[ramanujan_part1_ch7_entry15_vonstaudtclausen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry15Vonstaudtclausen.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry15_vonstaudtclausen_eq
  {r : ℂ}
  {x : ℝ}
-- given
  (hr : -1 < r.re)
  (hx0 : 0 < x)
  (hx1 : x < 1) :
-- imply
  ∃! L : ℂ,
    Tendsto (chapter7Entry15PartialSum r x) atTop (𝓝 L) ∧
    chapter7Entry15Left r x hx0 hx1 =
    -Complex.cos ((Real.pi : ℂ) * r / 2) * L := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry15Vonstaudtclausen.ramanujan_part1_ch7_entry15_vonstaudtclausen r x hr hx0 hx1


-- created on 2026-10-20
