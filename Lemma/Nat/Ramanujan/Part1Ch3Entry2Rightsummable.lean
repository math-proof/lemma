import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry2Rightsummable
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry2Rightsummable


/--
[ramanujan_part1_ch3_entry2_rightsummable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Rightsummable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry2_rightsummable_eq
  {x z : ℂ}
-- given
  (hz : ∀ r : ℕ, z + (r : ℂ) ≠ 0) :
-- imply
  Summable (fun j : ℕ =>
    ((-1 : ℂ) ^ j * x ^ (j + 1) / (∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Rightsummable.ramanujan_part1_ch3_entry2_rightsummable x z hz


-- created on 2026-10-20
