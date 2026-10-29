import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Nat.Ramanujan.Part1Ch2Entry7
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5First

/--
[ramanujan_part1_ch2_entry7_example5_first](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5First.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry7_example5_first
  :
-- imply
  HasSum (fun n : ℕ => Real.arctan (1 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2))) (Real.pi / 4) := by
-- proof
  have hnn : ∀ i : ℕ, 0 ≤ Real.arctan (1 / (2 * ((i + 1 : ℕ) : ℝ) ^ 2)) := by
    intro i
    rw [Real.arctan_nonneg]
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : ∀ r : ℕ, ∑ k ∈ Finset.range r, Real.arctan (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 2))
    = Real.arctan ((r : ℝ) / (r + 1)) := by
    intro r
    have hr : (0 : ℝ) < r + 1 := by positivity
    rw [show (r : ℝ) / (r + 1) = 2 * (r : ℝ) / (1 ^ 2 + 2 * 1 * (r : ℝ) + 1) by field_simp; ring,
      ← Entry7.ramanujan_part1_ch2_entry7 1 r one_pos]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hps]
  rw [← Real.arctan_one]
  exact (Real.continuous_arctan.tendsto _).comp (tendsto_natCast_div_add_atTop 1)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5First


-- created on 2026-10-20
-- updated on 2026-10-28
