import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry11CorollaryPowerSummable
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry11CorollaryPowerSummable


/--
[ramanujan_part1_ch3_entry11_corollary_power_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry11CorollaryPowerSummable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry11_corollary_power_summable_eq
  {a : ℕ → ℂ}
  {n : ℕ}
-- given
  (ha : Summable (fun j => ‖a j‖))
  (hn : 1 ≤ n) :
-- imply
  Summable (fun j => ‖(a j) ^ n‖) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry11CorollaryPowerSummable.ramanujan_part1_ch3_entry11_corollary_power_summable a ha n hn


-- created on 2026-10-20
