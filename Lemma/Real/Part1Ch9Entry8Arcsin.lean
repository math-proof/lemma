import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch9Entry8Arcsin

open Ramanujan.Part1Ch9.Entry8Arcsin

/--
[Part1Ch9Entry8Arcsin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry8Arcsin.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry8_arcsin_eq
-- given
  (x : ℝ)
  (hx : |x| < 1) :
-- imply
  0 < 1 - x ∧
    2 - x ≠ 0 ∧
    |x / (2 - x)| < 1 ∧
    Summable (chapter9Entry8FTerm (x / (2 - x))) ∧
    Summable (chapter9Entry8DilogTerm x) ∧
    chapter9Entry8F (x / (2 - x)) =
      (1 / 8 : ℝ) * Real.log (1 - x) ^ 2 +
        (1 / 2 : ℝ) * chapter9Entry8Dilog x := by
-- proof
  apply Ramanujan.Part1Ch9.Entry8Arcsin.ramanujan_part1_ch9_entry8_arcsin x hx

-- created on 2026-10-10
