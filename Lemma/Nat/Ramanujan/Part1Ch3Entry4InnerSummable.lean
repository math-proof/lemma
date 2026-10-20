import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry4InnerSummable
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry4InnerSummable


/--
[ramanujan_part1_ch3_entry4_inner_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4InnerSummable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry4_inner_summable_eq
  {x : ℂ}
  {n : ℕ} :
-- imply
  Summable (fun j : ℕ => ‖((j + 1 : ℂ) ^ n * x ^ (j + 1) / (Nat.factorial j : ℂ))‖) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4InnerSummable.ramanujan_part1_ch3_entry4_inner_summable x n


-- created on 2026-10-20
