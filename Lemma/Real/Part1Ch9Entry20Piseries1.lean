import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch9Entry20Piseries1

open Ramanujan.Part1Ch9.Entry20Piseries1

/--
[Part1Ch9Entry20Piseries1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry20Piseries1.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry20_piseries1_eq
-- given
  (x : ℝ)
  (hx : |x| ≤ Real.pi / 2) :
-- imply
  (x ≠ 0 → 0 < |2 * Real.sin x|) ∧
    Summable chapter9ZetaThreeTerm ∧
    Summable (chapter9Entry23FactorialTerm x) ∧
    Summable (chapter9SineFourierTwoTerm x) ∧
    Summable (chapter9CosineFourierThreeTerm x) ∧
    (∑' k : ℕ, chapter9Entry23FactorialTerm x k) =
      chapter9Entry20LogTerm x +
        x / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm x j +
        (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm x j -
        chapter9ZetaThree / 4 := by
-- proof
  apply Ramanujan.Part1Ch9.Entry20Piseries1.ramanujan_part1_ch9_entry20_piseries1 x hx

-- created on 2026-10-10
