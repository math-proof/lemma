import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10Example4Summable
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry10Example4Summable


/--
[ramanujan_part1_ch3_entry10_example4_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example4Summable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry10_example4_summable_eq
  {x : ℝ} :
-- imply
  Summable (fun k : ℕ => Real.exp (-x) * x ^ k *
        (∑ j ∈ Finset.Icc (1 : ℕ) k, (1 : ℝ) / (j : ℝ)) / (Nat.factorial k : ℝ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example4Summable.ramanujan_part1_ch3_entry10_example4_summable x


-- created on 2026-10-20
