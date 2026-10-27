import Mathlib
import Initialize.Tactic.Attr.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Rightsummable

/--
[ramanujan_entry2_norm_term](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Rightsummable.lean)
-/
@[path]
private lemma ramanujan_entry2_norm_term (x z : ℂ) (m : ℕ) :
  ‖((-1 : ℂ) ^ m * x ^ (m + 1) / ∏ k ∈ Finset.range (m + 1), (z + (k : ℂ)))‖
    = ‖x‖ ^ (m + 1) / ‖∏ k ∈ Finset.range (m + 1), (z + (k : ℂ))‖ := by
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Rightsummable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Rightsummable

/--
[ramanujan_entry2_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Rightsummable.lean)
-/
@[path]
private lemma ramanujan_entry2_ratio (x z : ℂ) (hz : ∀ r : ℕ, z + (r : ℂ) ≠ 0) (hx : x ≠ 0)
  (j : ℕ) :
  ‖((-1 : ℂ) ^ (j + 1) * x ^ (j + 1 + 1) / ∏ k ∈ Finset.range (j + 1 + 1), (z + (k : ℂ)))‖
    / ‖((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ)))‖
    = ‖x‖ / ‖z + ((j + 1 : ℕ) : ℂ)‖ := by
  rw [ramanujan_entry2_norm_term, ramanujan_entry2_norm_term]
  have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hP : (0 : ℝ) < ‖∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))‖ := by
    rw [norm_pos_iff]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hz k)
  have hq : (0 : ℝ) < ‖z + ((j + 1 : ℕ) : ℂ)‖ :=
    norm_pos_iff.mpr (hz (j + 1))
  have hsplit : (∏ k ∈ Finset.range (j + 1 + 1), (z + (k : ℂ)))
    = (∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))) * (z + ((j + 1 : ℕ) : ℂ)) :=
    Finset.prod_range_succ (fun k => z + (k : ℂ)) (j + 1)
  rw [hsplit, norm_mul]
  have hA : ‖x‖ ^ (j + 1) ≠ 0 := ne_of_gt (pow_pos hpos _)
  have hpow : ‖x‖ ^ (j + 1 + 1) = ‖x‖ ^ (j + 1) * ‖x‖ := pow_succ _ _
  rw [hpow]
  have hP' : ‖∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))‖ ≠ 0 := ne_of_gt hP
  have hq' : ‖z + ((j + 1 : ℕ) : ℂ)‖ ≠ 0 := ne_of_gt hq
  have hx' : ‖x‖ ≠ 0 := ne_of_gt hpos
  field_simp

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Rightsummable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Rightsummable

/--
[ramanujan_entry2_denom_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Rightsummable.lean)
-/
@[path]
private lemma ramanujan_entry2_denom_atTop (z : ℂ) :
  Filter.Tendsto (fun j : ℕ => ‖z + ((j + 1 : ℕ) : ℂ)‖) Filter.atTop Filter.atTop := by
  have hbase : Filter.Tendsto (fun j : ℕ => ((j : ℝ) + 1) - ‖z‖) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    have hev : ∀ᶠ j : ℕ in Filter.atTop, b + ‖z‖ ≤ (j : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (b + ‖z‖)
    filter_upwards [hev] with j hj
    linarith
  refine Filter.tendsto_atTop_mono (fun j => ?_) hbase
  have hcast : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  have hnorm : ‖(((j + 1 : ℕ)) : ℂ)‖ = (((j + 1 : ℕ)) : ℝ) := Complex.norm_natCast _
  have htri := norm_sub_norm_le ((((j + 1 : ℕ))) : ℂ) (-z)
  rw [sub_neg_eq_add, norm_neg, hnorm, hcast, add_comm ((((j + 1 : ℕ))) : ℂ)] at htri
  linarith

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Rightsummable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Rightsummable

/--
[ramanujan_part1_ch3_entry2_rightsummable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Rightsummable.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry2_rightsummable
  {x z : ℂ}
-- given
  (hz : ∀ r : ℕ, z + (r : ℂ) ≠ 0) :
-- imply
  Summable (fun j : ℕ =>
    ((-1 : ℂ) ^ j * x ^ (j + 1) / (∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))))) := by
-- proof
  by_cases hx0 : x = 0
  · have hzero : (fun j : ℕ => ((-1 : ℂ) ^ j * x ^ (j + 1) /
    (∏ k ∈ Finset.range (j + 1), (z + (k : ℂ))))) = fun _ => 0 := by
    funext j
    rw [pow_succ, hx0]
    simp
    rwa [hzero]
  · refine summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one ?_ ?_
    · apply Filter.Eventually.of_forall
      intro j
      apply div_ne_zero
      · apply mul_ne_zero
        · exact pow_ne_zero _ (by norm_num)
        · exact pow_ne_zero _ hx0
      · exact Finset.prod_ne_zero_iff.mpr (fun k _ => hz k)
    · have hlim : Filter.Tendsto (fun j : ℕ => ‖x‖ / ‖z + ((j + 1 : ℕ) : ℂ)‖)
      Filter.atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop (ramanujan_entry2_denom_atTop z) ‖x‖
      exact hlim.congr (fun j => (ramanujan_entry2_ratio x z hz hx0 j).symm)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Rightsummable


-- created on 2026-10-20
-- updated on 2026-10-26
