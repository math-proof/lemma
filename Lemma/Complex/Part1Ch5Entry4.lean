import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch5Entry4

open Ramanujan.Part1Ch5.Entry4

/--
[Part1Ch5Entry4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry4.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry4_eq
-- given
  (p : ℂ)
  (hp : ‖p‖ < 1)
  (n : ℕ) :
-- imply
  p + 1 ≠ 0 ∧
    Summable (chapter5Entry4Term n p) ∧
    chapter5Psi n p / (p + 1) ^ (n + 1) =
      ∑' k : ℕ, chapter5Entry4Term n p k := by
-- proof
  apply Ramanujan.Part1Ch5.Entry4.ramanujan_part1_ch5_entry4 n p hp

-- created on 2026-10-10
