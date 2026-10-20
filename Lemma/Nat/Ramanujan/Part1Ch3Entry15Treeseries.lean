import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry15Treeseries
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry15Treeseries


/--
[ramanujan_part1_ch3_entry15_treeseries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry15Treeseries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry15_treeseries_eq
  {x u : ℝ}
-- given
  (hu_pos : 0 < u)
  (hu_lt : u < 1)
  (hu_eq : u - Real.log u = 1 + x ^ 2 / 2) :
-- imply
  HasSum (fun k : ℕ => ((k + 1 : ℝ) ^ (k - 1) / (Nat.factorial k : ℝ)) *
    Real.exp (-(k : ℝ) * (1 + x ^ 2 / 2)))
    (u * Real.exp (1 + x ^ 2 / 2)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry15Treeseries.ramanujan_part1_ch3_entry15_treeseries x u hu_pos hu_lt hu_eq


-- created on 2026-10-20
