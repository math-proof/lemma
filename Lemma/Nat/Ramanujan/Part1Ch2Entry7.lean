import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7


/--
[ramanujan_part1_ch2_entry7](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_eq
  {n : ℝ}
  {r : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∑ k ∈ Finset.range r, Real.arctan (2 / (n + 2 * (k : ℝ) + 1) ^ 2) =
      Real.arctan (2 * (r : ℝ) / (n ^ 2 + 2 * n * (r : ℝ) + 1)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7.ramanujan_part1_ch2_entry7 n r hn


-- created on 2026-10-20
