import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry31Ramanujansum
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry31Ramanujansum


/--
[ramanujan_part1_ch9_entry31_ramanujansum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry31_ramanujansum_eq
  {x : ℝ}
-- given
  (hxLower : 0 ≤ x)
  (hxUpper : x ≤ 1 / 4) :
-- imply
  Summable (chapter9PsiTerm (1 / 2 - x)) ∧
    Summable (chapter9PsiTerm (2 * x)) ∧
    Summable (chapter9PsiTerm x) ∧
    0 < 2 * Real.cos (Real.pi * x) ∧
    (∑' k : ℕ, chapter9PsiTerm (1 / 2 - x) k) +
    (1 / 2 : ℝ) * ∑' k : ℕ, chapter9PsiTerm (2 * x) k -
    ∑' k : ℕ, chapter9PsiTerm x k =
    Real.pi / 2 * Real.log (2 * Real.cos (Real.pi * x)) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum.ramanujan_part1_ch9_entry31_ramanujansum x hxLower hxUpper


-- created on 2026-10-20
