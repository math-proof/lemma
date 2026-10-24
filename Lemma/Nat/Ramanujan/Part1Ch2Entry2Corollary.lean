import Mathlib
import sympy.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[harm_succ_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma harm_succ_real (n : ℕ) :
  ((harmonic (n + 1) : ℚ) : ℝ) = ((harmonic n : ℚ) : ℝ) + 1 / ((n : ℝ) + 1) := by
  have h := harmonic_succ n
  have h2 : ((harmonic (n + 1) : ℚ) : ℝ) = ((harmonic n + ((n + 1 : ℕ) : ℚ)⁻¹ : ℚ) : ℝ) := by rw [h]
  rw [h2]
  push_cast
  congr 1
  ring_nf

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[pf_id2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma pf_id2 (n : ℝ) (hn : n ≠ 0) (h1 : 3 * n - 1 ≠ 0) (h2 : 3 * n + 1 ≠ 0) :
  1 / ((3 * n) ^ 3 - 3 * n)
    = -1 / (3 * n) + (1/2) * (1 / (3 * n - 1)) + (1/2) * (1 / (3 * n + 1)) := by
  have hfac : (3 * n) ^ 3 - 3 * n = 3 * n * (3 * n - 1) * (3 * n + 1) := by ring
  rw [hfac]
  field_simp
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[sum_ident](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma sum_ident (N : ℕ) :
  ∑ j ∈ Finset.range N, (1 : ℝ) / ((3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1))
    = (((harmonic (3 * N + 1) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hn : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h1 : 3 * ((k : ℝ) + 1) - 1 ≠ 0 := by
      have h : 3 * ((k : ℝ) + 1) - 1 = 3 * (k : ℝ) + 2 := by ring
      rw [h]
      positivity
    have h2 : 3 * ((k : ℝ) + 1) + 1 ≠ 0 := by positivity
    rw [pf_id2 _ hn h1 h2]
    have e2 := harm_succ_real k
    have e1a := harm_succ_real (3 * k + 1)
    have e1b := harm_succ_real (3 * k + 1 + 1)
    have e1c := harm_succ_real (3 * k + 1 + 1 + 1)
    have hk1 : 3 * (k + 1) + 1 = (3 * k + 1 + 1 + 1) + 1 := by ring
    rw [hk1, e1c, e1b, e1a, e2]
    push_cast
    have d1 : 3 * ((k : ℝ) + 1) - 1 = (3 * (k : ℝ) + 1) + 1 := by ring
    have d2 : 3 * ((k : ℝ) + 1) + 1 = (3 * (k : ℝ) + 1) + 3 := by ring
    have d3 : 3 * ((k : ℝ) + 1) = (3 * (k : ℝ) + 1) + 2 := by ring
    rw [d1, d2, d3]
    have h33 : ((3 : ℝ) * (k : ℝ) + 1) + 2 ≠ 0 := by positivity
    have h_eq : ((3 : ℝ) * (k : ℝ) + 1) + 2 = 3 * ((k : ℝ) + 1) := by ring
    have e3 : (1 : ℝ) / ((k : ℝ) + 1) = 3 * (1 / (((3 : ℝ) * (k : ℝ) + 1) + 2)) := by
      rw [h_eq]
      field_simp
    rw [e3]
    ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[denom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma denom_pos (j : ℕ) : (0 : ℝ) < (3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1) := by
  have hj : (1 : ℝ) ≤ ((j : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  nlinarith [hj, sq_nonneg ((j : ℝ) + 1)]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[term_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma term_le (j : ℕ) :
  (1 : ℝ) / ((3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1))
    ≤ 1 / ((((j : ℝ)) + 1) ^ 2) := by
  apply one_div_le_one_div_of_le (by positivity)
  have hj : (1 : ℝ) ≤ ((j : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  nlinarith [hj, sq_nonneg ((j : ℝ) + 1)]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[summable_major](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma summable_major : Summable (fun j : ℕ => (1 : ℝ) / ((((j : ℝ)) + 1) ^ 2)) := by
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) 1).mpr h2
  refine hshift.congr (fun j => ?_)
  simp

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[summable_target](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma summable_target : Summable (fun j : ℕ => (1 : ℝ) / ((3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1))) := by
  apply Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) summable_major
  · exact le_of_lt (one_div_pos.mpr (denom_pos j))
  · exact term_le j

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[tend_3N1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma tend_3N1 : Filter.Tendsto (fun N : ℕ => 3 * N + 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with N hN
  omega

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[tend_h3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma tend_h3 : Filter.Tendsto (fun N : ℕ => ((harmonic (3 * N + 1) : ℚ) : ℝ) - Real.log (((3 * N + 1 : ℕ)) : ℝ)) Filter.atTop (nhds Real.eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log.comp tend_3N1

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[logdiff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma logdiff_eq (N : ℕ) (hN : 1 ≤ N) :
  Real.log (((3 * N + 1 : ℕ)) : ℝ) - Real.log ((N : ℝ))
    = Real.log (3 + 1 / ((N : ℕ) : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := Nat.lt_of_lt_of_le (by norm_num) hN
    exact Nat.cast_pos.mpr this
  have h3N1 : (((3 * N + 1 : ℕ)) : ℝ) = 3 * (N : ℝ) + 1 := by push_cast; ring
  rw [h3N1]
  have hNe : ((N : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  have h3Ne : (3 : ℝ) * (N : ℝ) + 1 ≠ 0 := by positivity
  rw [← Real.log_div h3Ne hNe]
  congr 1
  field_simp

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[tend_logdiff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma tend_logdiff : Filter.Tendsto (fun N : ℕ => Real.log (((3 * N + 1 : ℕ)) : ℝ) - Real.log ((N : ℕ) : ℝ)) Filter.atTop (nhds (Real.log 3)) := by
  have hcont : ContinuousAt Real.log 3 := Real.continuousAt_log (by norm_num)
  have h0 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℕ) : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h3 : Filter.Tendsto (fun _ : ℕ => (3 : ℝ)) Filter.atTop (nhds 3) := tendsto_const_nhds
  have hinter : Filter.Tendsto (fun N : ℕ => (3 : ℝ) + 1 / ((N : ℕ) : ℝ)) Filter.atTop (nhds 3) := by
    have h := h3.add h0
    simpa [add_comm] using h
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (3 + 1 / ((N : ℕ) : ℝ))) Filter.atTop (nhds (Real.log 3)) :=
    hcont.tendsto.comp hinter
  apply Filter.Tendsto.congr' _ hlog
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN using (logdiff_eq N hN).symm

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[tend_partial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma tend_partial :
  Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (1 : ℝ) / ((3 * (((j : ℝ)) + 1)) ^ 3 - 3 * (((j : ℝ)) + 1)))
    Filter.atTop (nhds ((Real.log 3 - 1) / 2)) := by
  have hA := Real.tendsto_harmonic_sub_log
  have hC := tend_logdiff
  have hcomb : Filter.Tendsto (fun N : ℕ =>
    ((((harmonic (3 * N + 1) : ℚ) : ℝ) - Real.log (((3 * N + 1 : ℕ)) : ℝ))
      - (((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ)))
      + (Real.log (((3 * N + 1 : ℕ)) : ℝ) - Real.log ((N : ℝ))) - 1) / 2)
    Filter.atTop (nhds ((Real.eulerMascheroniConstant - Real.eulerMascheroniConstant + Real.log 3 - 1) / 2)) := by
    exact ((tend_h3.sub hA).add hC).sub_const 1 |>.div_const 2
  have hlim : (Real.eulerMascheroniConstant - Real.eulerMascheroniConstant + Real.log 3 - 1) / 2 = (Real.log 3 - 1) / 2 := by ring
  rw [hlim] at hcomb
  have hcomb2 : Filter.Tendsto (fun N : ℕ => ((((harmonic (3 * N + 1) : ℚ) : ℝ) - ((harmonic N : ℚ) : ℝ) - 1) / 2))
    Filter.atTop (nhds ((Real.log 3 - 1) / 2)) := by
    apply Filter.Tendsto.congr (fun N => ?_) hcomb
    ring
  exact Filter.Tendsto.congr (fun N => (sum_ident N).symm) hcomb2

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary

/--
[ramanujan_part1_ch2_entry2_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry2_corollary
  :
-- imply
  HasSum (fun j : ℕ => (1 : ℝ) / ((3 * ((j : ℝ) + 1)) ^ 3 - 3 * ((j : ℝ) + 1)))
    ((Real.log 3 - 1) / 2) := by
-- proof
  exact summable_target.hasSum_iff_tendsto_nat.mpr tend_partial

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary


-- created on 2026-10-20
-- updated on 2026-10-23
