import Mathlib
import Initialize.Tactic.Attr.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example3

/--
[ramanujan_part1_ch2_entry7_example3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example3.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry7_example3
  {n : ℝ}
-- given
  (hn : 0 < n) :
-- imply
  HasSum (fun k : ℕ => Real.arctan (1 / (2 * (n + (k : ℝ) + 1) ^ 2)))
    (Real.arctan (1 / (2 * n + 1))) := by
-- proof
  have hnn : ∀ i : ℕ, 0 ≤ Real.arctan (1 / (2 * (n + (i : ℝ) + 1) ^ 2)) := by
    intro i
    rw [Real.arctan_nonneg]
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : ∀ r : ℕ, ∑ k ∈ Finset.range r, Real.arctan (1 / (2 * (n + (k : ℝ) + 1) ^ 2))
    = Real.arctan (2 * (r : ℝ) / ((2 * n + 1) ^ 2 + 2 * (2 * n + 1) * (r : ℝ) + 1)) := by
    intro r
    rw [← Entry7.ramanujan_part1_ch2_entry7 (2 * n + 1) r (by linarith)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    field_simp
    ring
  simp_rw [hps]
  have hlim : Filter.Tendsto
    (fun r : ℕ => 2 * (r : ℝ) / ((2 * n + 1) ^ 2 + 2 * (2 * n + 1) * (r : ℝ) + 1))
    Filter.atTop (nhds (1 / (2 * n + 1))) := by
    have h := (tendsto_natCast_div_add_atTop
      (((2 * n + 1) ^ 2 + 1) / (2 * (2 * n + 1)) : ℝ)).const_mul (1 / (2 * n + 1))
    rw [mul_one] at h
    refine h.congr fun r => ?_
    have : (0 : ℝ) < 2 * n + 1 := by linarith
    field_simp
    ring
  exact (Real.continuous_arctan.tendsto _).comp hlim

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example3


-- created on 2026-10-20
-- updated on 2026-10-26
