import Mathlib
import Initialize.Tactic.Attr.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example1SumPositiveEventually

/--
[ramanujan_part1_ch3_entry10_example1_sum_positive_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example1SumPositiveEventually.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry10_example1_sum_positive_eventually
  :
-- imply
  ∀ᶠ (x : ℝ) in Filter.atTop, 0 < ∑' (j : ℕ), x ^ (j + 1) * Real.sqrt (↑(j + 1)) /
    (↑(Nat.factorial (j + 1)) : ℝ) := by
-- proof
  filter_upwards [
    Entry10Example1SummableEventually.ramanujan_part1_ch3_entry10_example1_summable_eventually,
    Filter.eventually_gt_atTop 0] with x hs hx
  refine hs.tsum_pos (fun j => by positivity) 0 ?_
  apply div_pos
  · apply mul_pos (pow_pos hx (0 + 1))
    exact Real.sqrt_pos.mpr (by positivity)
  · exact_mod_cast Nat.factorial_pos (0 + 1)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry10Example1SumPositiveEventually


-- created on 2026-10-20
-- updated on 2026-10-26
