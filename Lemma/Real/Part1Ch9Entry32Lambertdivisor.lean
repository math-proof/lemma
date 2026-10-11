import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch9Entry32Lambertdivisor

open Ramanujan.Part1Ch9.Entry32Lambertdivisor

/--
[Part1Ch9Entry32Lambertdivisor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry32Lambertdivisor.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry32_lambert_divisor_eq
-- given
  (x : ℝ)
  (hx : |x| ≤ Real.pi / 4) :
-- imply
  0 < Real.cos x ∧
    Summable (chapter9Entry32LeftTerm x) ∧
    Summable (chapter9Entry19TanTerm x) ∧
    (∑' k : ℕ, chapter9Entry32LeftTerm x k) =
      2 * ∑' k : ℕ, chapter9Entry19TanTerm x k := by
-- proof
  apply Ramanujan.Part1Ch9.Entry32Lambertdivisor.ramanujan_part1_ch9_entry32_lambertdivisor x hx

-- created on 2026-10-10
