/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example1SumPositiveEventually.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Positivity
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry10Example1SummableEventually
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 10, Example 1

Eventual positivity of ∑ xʲ⁺¹√(j+1)/(j+1)!.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example1SumPositiveEventually

/-- Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, Example 1, printed p.
    64 / PDF p. 74.

Proves `Wanted` entry `ramanujan_part1_ch3_entry10_example1_sum_positive_eventually`.
-/
theorem ramanujan_part1_ch3_entry10_example1_sum_positive_eventually :
    ∀ᶠ (x : ℝ) in Filter.atTop, 0 < ∑' (j : ℕ), x ^ (j + 1) * Real.sqrt (↑(j + 1)) /
        (↑(Nat.factorial (j + 1)) : ℝ) := by
  filter_upwards [
    Entry10Example1SummableEventually.ramanujan_part1_ch3_entry10_example1_summable_eventually,
    Filter.eventually_gt_atTop 0] with x hs hx
  refine hs.tsum_pos (fun j => by positivity) 0 ?_
  apply div_pos
  · apply mul_pos (pow_pos hx (0 + 1))
    exact Real.sqrt_pos.mpr (by positivity)
  · exact_mod_cast Nat.factorial_pos (0 + 1)

end Entry10Example1SumPositiveEventually

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
