import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10Example2Summable
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry10Example2Summable


/--
[ramanujan_part1_ch3_entry10_example2_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example2Summable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry10_example2_summable_eq
  :
-- imply
  ∀ (x : ℝ),
        Summable (fun j : ℕ => Real.exp (-x) * x ^ (j + 1) * Real.log ((j : ℝ) + 2) /
            (Nat.factorial (j + 1) : ℝ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example2Summable.ramanujan_part1_ch3_entry10_example2_summable


-- created on 2026-10-20
