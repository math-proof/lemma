import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10Example1SummableEventually
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry10Example1SummableEventually


/--
[ramanujan_part1_ch3_entry10_example1_summable_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example1SummableEventually.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry10_example1_summable_eventually_eq
  :
-- imply
  ∀ᶠ (x : ℝ) in Filter.atTop,
        Summable (fun j : ℕ => x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) /
            (↑(Nat.factorial (j + 1)) : ℝ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example1SummableEventually.ramanujan_part1_ch3_entry10_example1_summable_eventually


-- created on 2026-10-20
