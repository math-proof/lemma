import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry17Sec
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry17Sec


/--
[ramanujan_part1_ch9_entry17_sec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry17Sec.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry17_sec_eq
  {x : ℝ}
-- given
  (hx : |x| ≤ Real.pi / 4) :
-- imply
  Real.cos x ≠ 0 ∧
    Summable (Entry32Lambertdivisor.chapter9Entry19TanTerm x) ∧
    Summable (Entry21Piseries2.chapter9Entry21SineTerm x) ∧
    (∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm x k) =
    chapter9XLogAbsTan x +
    ∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm x k := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry17Sec.ramanujan_part1_ch9_entry17_sec x hx


-- created on 2026-10-20
