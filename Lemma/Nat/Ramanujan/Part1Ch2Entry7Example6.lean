import Mathlib
import sympy.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example6

/--
[arctan_sqrt_two_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example6.lean)
-/
@[path]
private lemma arctan_sqrt_two_sub_one : Real.arctan (Real.sqrt 2 - 1) = Real.pi / 8 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : 1 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hadd := Real.arctan_add (x := Real.sqrt 2 - 1) (y := Real.sqrt 2 - 1) (by nlinarith)
  have hone : (Real.sqrt 2 - 1 + (Real.sqrt 2 - 1)) / (1 - (Real.sqrt 2 - 1) * (Real.sqrt 2 - 1))
    = 1 := by
    rw [div_eq_one_iff_eq (by nlinarith)]
    linear_combination h2
  rw [hone, Real.arctan_one] at hadd
  linarith

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example6

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example6

/--
[ramanujan_part1_ch2_entry7_example6](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example6.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry7_example6
  :
-- imply
  HasSum (fun k : ℕ => Real.arctan (1 / ((1 + Real.sqrt 2 * (↑(k + 1) : ℝ)) ^ 2)))
    (Real.pi / 8) := by
-- proof
  set n : ℝ := 1 + Real.sqrt 2 with hn_def
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 < n := by positivity
  have hterm (k : ℕ) :
    2 / (n + 2 * (k : ℝ) + 1) ^ 2 = 1 / (1 + Real.sqrt 2 * (↑(k + 1) : ℝ)) ^ 2 := by
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (2 * ((k : ℝ) + 1) ^ 2 - 1) * h2
  have hinv : n⁻¹ = Real.sqrt 2 - 1 := inv_eq_of_mul_eq_one_left (by linear_combination h2)
  have hlim : Filter.Tendsto (fun r : ℕ => Real.arctan (2 * (r : ℝ) / (n ^ 2 + 2 * n * r + 1)))
    Filter.atTop (nhds (Real.pi / 8)) := by
    have h := (tendsto_natCast_div_add_atTop ((n ^ 2 + 1) / (2 * n))).const_mul n⁻¹
    rw [mul_one, hinv] at h
    rw [← arctan_sqrt_two_sub_one]
    refine (Real.continuous_arctan.tendsto _).comp (h.congr fun r => ?_)
    have hr : (0 : ℝ) < r + (n ^ 2 + 1) / (2 * n) := by positivity
    rw [← hinv]
    field_simp
    ring
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun k => Real.arctan_nonneg.mpr (by positivity)) _).2 ?_
  refine hlim.congr fun r => ?_
  simp_rw [← hterm]
  exact (Entry7.ramanujan_part1_ch2_entry7 n r hn).symm

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example6


-- created on 2026-10-20
-- updated on 2026-10-23
