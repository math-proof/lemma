/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch8Entry15Doublegamma.lean -/


import Def.Analysis.Ramanujan.Part1Ch8Entry15Doublegamma
import Lemma.Real.Ramanujan.Part1Ch8Entry15Doublegamma
import Mathlib.Analysis.Asymptotics.Lemmas


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch8Entry15Doublegamma

open Asymptotics Filter Complex

open MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry15Doublegamma

-- At exponent `1/4`, discarding the sixth- and eighth-order terms leaves an `O(a⁻⁴)` error.
example :
    (fun x : ℝ => ((((x + 1 / 2) / chapter8Entry15A x : ℝ) : ℂ)) - 1 +
      1 / (24 * (chapter8Entry15A x : ℂ) ^ 2)) =O[atTop]
      (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 4) := by
  have hentry := ramanujan_part1_ch8_entry15_doublegamma (1 / 4 : ℂ)
  have hA : Tendsto chapter8Entry15A atTop atTop := hentry.1
  have h84 : (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 8) =O[atTop]
      (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 4) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hA.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
    have ha : 0 < chapter8Entry15A x := Real.exp_pos _
    simp only [norm_div, norm_one, norm_pow, Complex.norm_real, one_mul]
    rw [Real.norm_eq_abs, abs_of_pos ha]
    apply (div_le_div_iff₀ (pow_pos ha 8) (pow_pos ha 4)).2
    have ha2 : 1 ≤ chapter8Entry15A x ^ 4 := one_le_pow₀ hx
    calc
      1 * chapter8Entry15A x ^ 4 = chapter8Entry15A x ^ 4 := one_mul _
      _ ≤ chapter8Entry15A x ^ 4 * chapter8Entry15A x ^ 4 :=
        le_mul_of_one_le_right (pow_nonneg ha.le 4) ha2
      _ = 1 * chapter8Entry15A x ^ 8 := by ring
  have h64 : (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 6) =O[atTop]
      (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 4) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hA.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
    have ha : 0 < chapter8Entry15A x := Real.exp_pos _
    simp only [norm_div, norm_one, norm_pow, Complex.norm_real, one_mul]
    rw [Real.norm_eq_abs, abs_of_pos ha]
    apply (div_le_div_iff₀ (pow_pos ha 6) (pow_pos ha 4)).2
    have ha2 : 1 ≤ chapter8Entry15A x ^ 2 := one_le_pow₀ hx
    calc
      1 * chapter8Entry15A x ^ 4 = chapter8Entry15A x ^ 4 := one_mul _
      _ ≤ chapter8Entry15A x ^ 4 * chapter8Entry15A x ^ 2 :=
        le_mul_of_one_le_right (pow_nonneg ha.le 4) ha2
      _ = 1 * chapter8Entry15A x ^ 6 := by ring
  have hmain := hentry.2.trans h84
  have h4 := isBigO_const_mul_self
    ((10 * (1 / 4 : ℂ) ^ 2 + 11 * (1 / 4 : ℂ)) / 720)
    (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 4) atTop
  have h6 := h64.const_mul_left
    (-((70 * (1 / 4 : ℂ) ^ 3 + 231 * (1 / 4 : ℂ) ^ 2 + 891 * (1 / 4 : ℂ)) /
      90720))
  have htail : (fun x : ℝ => chapter8Entry15Approx (1 / 4 : ℂ) x - 1 +
      1 / (24 * (chapter8Entry15A x : ℂ) ^ 2)) =O[atTop]
      (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 4) := by
    have h := h4.add h6
    convert h using 1
    ext x
    have ha : (chapter8Entry15A x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    unfold chapter8Entry15Approx
    dsimp
    field_simp [ha]
    ring
  have h := hmain.add htail
  convert h using 1
  ext x
  have hp : chapter8Entry15Power (1 / 4 : ℂ) x =
      (((x + 1 / 2) / chapter8Entry15A x : ℝ) : ℂ) := by
    unfold chapter8Entry15Power
    norm_num
  rw [hp]
  ring

-- At exponent `1`, the frozen theorem gives the explicit sixth-order expansion.
example :
    (fun x : ℝ => chapter8Entry15Power 1 x -
      (1 - 1 / (6 * (chapter8Entry15A x : ℂ) ^ 2) +
        7 / (240 * (chapter8Entry15A x : ℂ) ^ 4) -
        149 / (11340 * (chapter8Entry15A x : ℂ) ^ 6))) =O[atTop]
      (fun x : ℝ => (1 : ℂ) / (chapter8Entry15A x : ℂ) ^ 8) := by
  have h := (ramanujan_part1_ch8_entry15_doublegamma (1 : ℂ)).2
  convert h using 1
  ext x
  unfold chapter8Entry15Approx
  dsimp
  ring

end MathlibExtTest.Analysis.Ramanujan.Part1Ch8Entry15Doublegamma
