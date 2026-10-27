import Mathlib
import Initialize.Tactic.Attr.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry11CorollaryPowerSummable

/--
[ramanujan_part1_ch3_entry11_corollary_power_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry11CorollaryPowerSummable.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry11_corollary_power_summable
  {a : ℕ → ℂ}
  {n : ℕ}
-- given
  (ha : Summable (fun j => ‖a j‖))
  (hn : 1 ≤ n) :
-- imply
  Summable (fun j => ‖(a j) ^ n‖) := by
-- proof
  have htend : Filter.Tendsto (fun j => ‖a j‖) Filter.atTop (nhds 0) :=
    ha.tendsto_atTop_zero
  have hev : ∀ᶠ j in Filter.atTop, ‖a j‖ < 1 :=
    htend.eventually (gt_mem_nhds zero_lt_one)
  have hpow : ∀ᶠ j in Filter.atTop, ‖(a j) ^ n‖ ≤ ‖a j‖ := by
    filter_upwards [hev] with j hj
    rw [norm_pow]
    exact pow_le_of_le_one (norm_nonneg _) (le_of_lt hj) (by omega)
  have hcof : ∀ᶠ j in Filter.cofinite, ‖(a j) ^ n‖ ≤ ‖a j‖ := by
    rwa [Nat.cofinite_eq_atTop]
  have hsum : Summable (fun j => (a j) ^ n) :=
    ha.of_norm_bounded_eventually hcof
  exact hsum.norm

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry11CorollaryPowerSummable


-- created on 2026-10-20
-- updated on 2026-10-26
