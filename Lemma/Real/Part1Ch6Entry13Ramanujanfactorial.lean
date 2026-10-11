import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch6Entry13Ramanujanfactorial

/--
[Part1Ch6Entry13Ramanujanfactorial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry13Ramanujanfactorial.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry13_ramanujanfactorial_eq
-- given
  (x : ℝ)
  (hx : 1 < |x|) :
-- imply
  (∀ j : ℕ, x ^ (j + 1) - 1 ≠ 0) ∧
    (∀ j : ℕ, x ^ ((j + 1) ^ 2) * (x ^ (2 * (j + 1)) - 1) ≠ 0) ∧
    Summable (fun j : ℕ => (-1 : ℝ) ^ (j + 2) / (x ^ (j + 1) - 1)) ∧
    Summable (fun j : ℕ =>
      ((-1 : ℝ) ^ (j + 2) * (x ^ (2 * (j + 1)) + 1)) /
        (x ^ ((j + 1) ^ 2) * (x ^ (2 * (j + 1)) - 1))) ∧
    ∑' j : ℕ, (-1 : ℝ) ^ (j + 2) / (x ^ (j + 1) - 1) =
      ∑' j : ℕ,
        ((-1 : ℝ) ^ (j + 2) * (x ^ (2 * (j + 1)) + 1)) /
          (x ^ ((j + 1) ^ 2) * (x ^ (2 * (j + 1)) - 1)) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry13Ramanujanfactorial.ramanujan_part1_ch6_entry13_ramanujanfactorial x hx

-- created on 2026-10-10
