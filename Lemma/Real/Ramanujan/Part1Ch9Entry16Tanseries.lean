import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry16Tanseries
open MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries
open scoped BigOperators
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry16Tanseries


/--
[ramanujan_part1_ch9_entry16_tanseries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry16_tanseries_eq
  {x : ℝ}
-- given
  (hx0 : 0 ≤ x)
  (hxUpper : x ≤ Real.pi / 4) :
-- imply
  0 < 2 * Real.cos x ∧
    Summable (chapter9Entry16DifferenceTerm x) ∧
    Summable (chapter9CentralSineTerm (2 * x)) ∧
    (∑' k : ℕ, chapter9Entry16DifferenceTerm x k) =
    Real.pi / 2 * Real.log (2 * Real.cos x) -
    (1 / 2 : ℝ) * ∑' k : ℕ, chapter9CentralSineTerm (2 * x) k := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries.ramanujan_part1_ch9_entry16_tanseries x hx0 hxUpper


-- created on 2026-10-20
