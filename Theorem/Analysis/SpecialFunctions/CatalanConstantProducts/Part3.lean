/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Def.Analysis.SpecialFunctions.CatalanConstantProducts.Part3


section

namespace MetaMathlibExt

/-- Even alternating unit sums vanish. -/
theorem catAlt_sum_zero (m : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2 * m), (-1 : ℝ) ^ (n + 1) = 0 := by
  induction m with
  | zero =>
    simp only [mul_zero]
    rw [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1)]
    simp only [Finset.sum_empty]
  | succ m ih =>
    have h1 := Finset.sum_Icc_succ_top (a := 1) (b := 2 * m + 1)
      (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1)) (by omega)
    have h2 := Finset.sum_Icc_succ_top (a := 1) (b := 2 * m)
      (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1)) (by omega)
    have heq : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [heq, h1, h2, ih]
    have eTop2 : (-1 : ℝ) ^ (((2 * m + 1)) + 1) = 1 := by
      have hexp : ((2 * m + 1 : ℕ)) + 1 = 2 * (m + 1) := by ring
      rw [hexp, pow_mul]
      norm_num
    have eTop1 : (-1 : ℝ) ^ (((2 * m + 1 + 1 : ℕ)) + 1) = -1 := by
      have hexp : ((2 * m + 1 + 1 : ℕ)) + 1 = 2 * (m + 1) + 1 := by ring
      rw [hexp, pow_succ, pow_mul]
      norm_num
    rw [eTop2, eTop1]
    norm_num

/-- Each log term as an integral. -/
theorem catTerm_eq_integral (n : ℕ) (hn : 1 ≤ n) :
    ((((n : ℤ) * (-1 : ℤ) ^ n : ℤ)) : ℝ) * Real.log (1 - 2 / (2 * (n : ℝ) + 1)) =
      (-1 : ℝ) ^ (n + 1) * (∫ u in (0 : ℝ)..1,
        ((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2))) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : ((((n : ℤ) * (-1 : ℤ) ^ n : ℤ)) : ℝ) = (n : ℝ) * (-1 : ℝ) ^ n := by
    push_cast
    ring
  have hbase : (1 : ℝ) - 2 / (2 * (n : ℝ) + 1)
      = (2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 1) := by
    have hne : (2 : ℝ) * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hpos1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hpos2 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hlog : Real.log (1 - 2 / (2 * (n : ℝ) + 1))
      = -Real.log ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1)) := by
    rw [hbase, Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2),
      Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos1)]
    ring
  have ha : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  have hint := catInt_integral (2 * (n : ℝ)) ha
  have harg : ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1))
      = ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1)) := rfl
  rw [hcast, hlog, hint]
  have hpow : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1) := pow_succ _ _
  rw [hpow]
  ring

/-- Log-sum as an integral of the finite alternating sum. -/
theorem catP_log_eq_integral (m : ℕ) :
    Real.log (catP m) = ∫ u in (0 : ℝ)..1, catFint (2 * m) u := by
  rw [catP_log]
  have hterm : ∀ n ∈ Finset.Icc 1 (2 * m),
      ((((n : ℤ) * (-1 : ℤ) ^ n : ℤ)) : ℝ) * Real.log (1 - 2 / (2 * (n : ℝ) + 1)) =
        ∫ u in (0 : ℝ)..1,
          (-1 : ℝ) ^ (n + 1) * (((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2))) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [catTerm_eq_integral n hn.1, intervalIntegral.integral_const_mul]
  rw [Finset.sum_congr rfl hterm]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro u hu
    have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
      Set.uIcc_of_le (by norm_num)
    rw [huIcc, Set.mem_Icc] at hu
    dsimp only []
    unfold catFint
    have hsplit : ∀ n ∈ Finset.Icc 1 (2 * m),
        (-1 : ℝ) ^ (n + 1) * (((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2))) =
          (-1 : ℝ) ^ (n + 1) +
            (-1 : ℝ) ^ (n + 1) * (u ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2)) := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have hub : u ^ 2 ≤ 1 := by
        have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
        calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
          _ ≤ 1 ^ 2 := by
              exact pow_le_pow_left₀ (abs_nonneg _) habs 2
          _ = 1 := one_pow 2
      have ha2 : (4 : ℝ) ≤ ((2 * (n : ℝ)) ^ 2) := by
        have h2n : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ (2 * (n : ℝ)) ^ 2 := by
              exact pow_le_pow_left₀ (by norm_num) h2n 2
      have hne : ((2 * (n : ℝ)) ^ 2 - u ^ 2) ≠ 0 := by linarith
      have hdiv : ((2 * (n : ℝ)) ^ 2 / (((2 * (n : ℝ)) ^ 2 - u ^ 2)))
          = 1 + u ^ 2 / (((2 * (n : ℝ)) ^ 2 - u ^ 2)) := by
        rw [div_eq_iff hne]
        have hcancel : (u ^ 2 / (((2 * (n : ℝ)) ^ 2 - u ^ 2))) * (((2 * (n : ℝ)) ^ 2 - u ^ 2))
            = u ^ 2 :=
          div_mul_cancel₀ _ hne
        have hmul : (1 + u ^ 2 / (((2 * (n : ℝ)) ^ 2 - u ^ 2))) * (((2 * (n : ℝ)) ^ 2 - u ^ 2))
            = (((2 * (n : ℝ)) ^ 2 - u ^ 2)) + u ^ 2 := by
          rw [add_mul, one_mul, hcancel]
        rw [hmul]
        ring
      calc (-1 : ℝ) ^ (n + 1) * (((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2)))
          = (-1 : ℝ) ^ (n + 1) * (1 + u ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2)) := by
            rw [hdiv]
        _ = (-1 : ℝ) ^ (n + 1) + (-1 : ℝ) ^ (n + 1) * (u ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2)) := by
            ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, catAlt_sum_zero m]
    simp only [zero_add]
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hcont : ContinuousOn
        (fun u : ℝ => (-1 : ℝ) ^ (n + 1) * (((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2))))
        (Set.Icc (0 : ℝ) 1) := by
      apply ContinuousOn.const_mul ?_
      apply ContinuousOn.div continuousOn_const ?_ ?_
      · exact (continuousOn_const.sub (ContinuousOn.pow continuousOn_id 2))
      · intro u hu
        simp only [Set.mem_Icc] at hu
        have hub : u ^ 2 ≤ 1 := by
          have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
          calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
            _ ≤ 1 ^ 2 := by
                exact pow_le_pow_left₀ (abs_nonneg _) habs 2
            _ = 1 := one_pow 2
        have ha2 : (4 : ℝ) ≤ ((2 * (n : ℝ)) ^ 2) := by
          have h2n : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
          calc (4 : ℝ) = 2 ^ 2 := by norm_num
            _ ≤ (2 * (n : ℝ)) ^ 2 := by
                exact pow_le_pow_left₀ (by norm_num) h2n 2
        linarith
    exact hcont.intervalIntegrable_of_Icc (by norm_num)

/-- Cot difference gives cosecant. -/
theorem catCsc_cot_diff (v : ℂ) (hv : Complex.sin v ≠ 0) :
    Complex.cot v - Complex.cot (2 * v) = 1 / Complex.sin (2 * v) := by
  unfold Complex.cot
  have hsin2 : Complex.sin (2 * v) = 2 * Complex.sin v * Complex.cos v := by
    rw [Complex.sin_two_mul]
  have hcos2 : Complex.cos (2 * v) = 2 * Complex.cos v ^ 2 - 1 := by
    rw [Complex.cos_two_mul]
  rw [hsin2, hcos2]
  field_simp
  ring

/-- Real points in `(0,1)` avoid the integers in `ℂ`. -/
theorem catMem_integerComplement (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hre : ((n : ℂ).re) = (((x : ℝ) : ℂ).re) := by rw [hn]
  simp only [Complex.intCast_re, Complex.ofReal_re] at hre
  have h0 : (0 : ℤ) < n := by
    have hpos : (0 : ℝ) < (n : ℝ) := by rw [hre]; exact hx0
    exact_mod_cast hpos
  have h1 : n < (1 : ℤ) := by
    have hlt : (n : ℝ) < (1 : ℝ) := by rw [hre]; exact hx1
    exact_mod_cast hlt
  omega

/-- Cosecant as cot difference, scaled by `π`. -/
theorem catCsc_pi_eq (z : ℂ) (hz2 : z / 2 ∈ Complex.integerComplement) :
    ((Real.pi : ℝ) : ℂ) * Complex.cot (((Real.pi : ℝ) : ℂ) * (z / 2))
      - ((Real.pi : ℝ) : ℂ) * Complex.cot (((Real.pi : ℝ) : ℂ) * z)
      = ((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) := by
  have hsin : Complex.sin (((Real.pi : ℝ) : ℂ) * (z / 2)) ≠ 0 :=
    sin_pi_mul_ne_zero hz2
  have hdiff := catCsc_cot_diff (((Real.pi : ℝ) : ℂ) * (z / 2)) hsin
  have h2v : 2 * (((Real.pi : ℝ) : ℂ) * (z / 2)) = ((Real.pi : ℝ) : ℂ) * z := by
    ring
  rw [h2v] at hdiff
  have hmul := congrArg (fun w : ℂ => ((Real.pi : ℝ) : ℂ) * w) hdiff
  simp only [mul_sub, mul_one_div] at hmul
  exact hmul

/-- Cosecant minus pole as a difference of cot series. -/
theorem catCsc_sub_eq (z : ℂ) (hz : z ∈ Complex.integerComplement)
    (hz2 : z / 2 ∈ Complex.integerComplement) :
    ((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) - 1 / z =
      ∑' n : ℕ, (cotTerm (z / 2) n - cotTerm z n) := by
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hpi := catCsc_pi_eq z hz2
  have hcot_z : ((Real.pi : ℝ) : ℂ) * Complex.cot (((Real.pi : ℝ) : ℂ) * z) - 1 / z =
      ∑' n : ℕ, cotTerm z n :=
    cot_series_rep' hz
  have hcot_z2 : ((Real.pi : ℝ) : ℂ) * Complex.cot (((Real.pi : ℝ) : ℂ) * (z / 2))
      - 1 / (z / 2) =
      ∑' n : ℕ, cotTerm (z / 2) n :=
    cot_series_rep' hz2
  have hdiv : (1 : ℂ) / (z / 2) = 2 / z := by
    field_simp
  have hb : Summable (fun n : ℕ => cotTerm (z / 2) n) :=
    summable_cotTerm hz2
  have ha : Summable (fun n : ℕ => cotTerm z n) :=
    summable_cotTerm hz
  have hsub : ∑' n : ℕ, (cotTerm (z / 2) n - cotTerm z n)
      = (∑' n : ℕ, cotTerm (z / 2) n) - ∑' n : ℕ, cotTerm z n :=
    (hb.hasSum.sub ha.hasSum).tsum_eq
  rw [hsub, ← hcot_z2, ← hcot_z, hdiv, ← hpi]
  ring

/-- Halved cot terms double the even cot terms. -/
theorem catCot_half_eq (z : ℂ) (n : ℕ) :
    cotTerm (z / 2) n = 2 * cotTerm z (2 * n + 1) := by
  unfold cotTerm
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  have heq1 : z / 2 - (((n : ℂ) + 1)) = (z - 2 * (((n : ℂ) + 1))) / 2 := by
    ring
  have heq2 : z / 2 + (((n : ℂ) + 1)) = (z + 2 * (((n : ℂ) + 1))) / 2 := by
    ring
  have hexp : 2 * (((n : ℂ) + 1)) = (2 * (n : ℂ) + 1) + 1 := by
    ring
  rw [heq1, heq2, one_div_div, one_div_div, hexp]
  ring

/-- Difference series equals alternating cot series. -/
theorem catCsc_even_odd (z : ℂ) (hz : z ∈ Complex.integerComplement)
    (hz2 : z / 2 ∈ Complex.integerComplement) :
    ∑' n : ℕ, (cotTerm (z / 2) n - cotTerm z n)
      = ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * cotTerm z n := by
  have hA : Summable (fun n : ℕ => cotTerm z n) := summable_cotTerm hz
  have hB : Summable (fun n : ℕ => cotTerm (z / 2) n) := summable_cotTerm hz2
  have hinj_even : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    dsimp only [] at h
    omega
  have hinj_odd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    dsimp only [] at h
    omega
  have hA_even : Summable (fun k : ℕ => cotTerm z (2 * k)) :=
    hA.comp_injective hinj_even
  have hA_odd : Summable (fun k : ℕ => cotTerm z (2 * k + 1)) :=
    hA.comp_injective hinj_odd
  have hB_eq : (fun n : ℕ => cotTerm (z / 2) n)
      = (fun n : ℕ => 2 * cotTerm z (2 * n + 1)) := by
    funext n
    exact catCot_half_eq z n
  have hB_tsum : (∑' n : ℕ, cotTerm (z / 2) n)
      = 2 * ∑' k : ℕ, cotTerm z (2 * k + 1) := by
    rw [hB_eq, tsum_mul_left]
  have hA_split : (∑' n : ℕ, cotTerm z n)
      = (∑' k : ℕ, cotTerm z (2 * k)) + ∑' k : ℕ, cotTerm z (2 * k + 1) := by
    rw [tsum_even_add_odd (f := fun n : ℕ => cotTerm z n) hA_even hA_odd]
  have hpow_even : ∀ k : ℕ, (-1 : ℂ) ^ ((2 * k) + 1) = -1 := by
    intro k
    rw [pow_succ, pow_mul]
    norm_num
  have hpow_odd : ∀ k : ℕ, (-1 : ℂ) ^ (((2 * k + 1)) + 1) = 1 := by
    intro k
    have hexp : ((2 * k + 1 : ℕ)) + 1 = 2 * (k + 1) := by ring
    rw [hexp, pow_mul]
    norm_num
  have hf_even_eq : (fun k : ℕ => (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k))
      = (fun k : ℕ => -(cotTerm z (2 * k))) := by
    funext k
    rw [hpow_even k]
    ring
  have hf_odd_eq : (fun k : ℕ => (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1))
      = (fun k : ℕ => cotTerm z (2 * k + 1)) := by
    funext k
    rw [hpow_odd k, one_mul]
  have hf_even : Summable (fun k : ℕ => (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k)) := by
    rw [hf_even_eq]
    exact hA_even.neg
  have hf_odd : Summable (fun k : ℕ => (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1)) := by
    rw [hf_odd_eq]
    exact hA_odd
  have hf : Summable (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n) :=
    Summable.even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      hf_even hf_odd
  have hf_split : (∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      = (∑' k : ℕ, (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k))
        + ∑' k : ℕ, (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1) := by
    rw [tsum_even_add_odd
      (f := fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n) hf_even hf_odd]
  rw [hf_split, hf_even_eq, hf_odd_eq]
  have hneg : (∑' k : ℕ, -(cotTerm z (2 * k)))
      = -(∑' k : ℕ, cotTerm z (2 * k)) := tsum_neg
  rw [hneg]
  have hdiff : ∑' n : ℕ, (cotTerm (z / 2) n - cotTerm z n)
      = (∑' n : ℕ, cotTerm (z / 2) n) - ∑' n : ℕ, cotTerm z n :=
    (hB.hasSum.sub hA.hasSum).tsum_eq
  rw [hdiff, hB_tsum, hA_split]
  ring

/-- Alternating cot terms as alternating reciprocal differences. -/
theorem catCotTerm_alt_eq (z : ℂ) (hz : z ∈ Complex.integerComplement)
    (n : ℕ) :
    (-1 : ℂ) ^ (n + 1) * cotTerm z n
      = 2 * z * (((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2)))) := by
  unfold cotTerm
  simp only [Nat.cast_add, Nat.cast_one]
  have hsub : (z - (((n : ℂ) + 1))) ≠ 0 := by
    have h := Complex.integerComplement_add_ne_zero hz (-(((n : ℤ) + 1)))
    simpa only [sub_eq_add_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Int.cast_neg, Nat.cast_add, Nat.cast_one] using h
  have hadd : (z + (((n : ℂ) + 1))) ≠ 0 := by
    have h := Complex.integerComplement_add_ne_zero hz (((n : ℤ) + 1))
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add,
      Nat.cast_one] using h
  have hpow : (z ^ 2 - (((n : ℂ) + 1) ^ 2)) ≠ 0 := by
    have h := Complex.integerComplement_pow_two_ne_pow_two hz (((n : ℤ) + 1))
    have heq : ((((n : ℤ) + 1) : ℤ) : ℂ) = (((n : ℂ) + 1)) := by
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [heq] at h
    exact sub_ne_zero.mpr h
  have hpow2 : ((((n : ℂ) + 1) ^ 2 - z ^ 2)) ≠ 0 := by
    have : ((((n : ℂ) + 1) ^ 2 - z ^ 2)) = -(z ^ 2 - (((n : ℂ) + 1) ^ 2)) := by
      ring
    rw [this]
    exact neg_ne_zero.mpr hpow
  have hpow_succ : (-1 : ℂ) ^ (n + 1) = (-1 : ℂ) ^ n * (-1) := pow_succ _ _
  rw [hpow_succ]
  field_simp
  ring

/-- Cosecant partial fractions with alternating signs. -/
theorem catCsc_tsum (z : ℂ) (hz : z ∈ Complex.integerComplement)
    (hz2 : z / 2 ∈ Complex.integerComplement) (hz0 : z ≠ 0) :
    ∑' n : ℕ, ((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2)))
      = ((((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) - 1 / z)
        / (2 * z)) := by
  have hsub := catCsc_sub_eq z hz hz2
  have heven := catCsc_even_odd z hz hz2
  have hA : Summable (fun n : ℕ => cotTerm z n) := summable_cotTerm hz
  have hinj_even : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    dsimp only [] at h
    omega
  have hinj_odd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    dsimp only [] at h
    omega
  have hA_even : Summable (fun k : ℕ => cotTerm z (2 * k)) :=
    hA.comp_injective hinj_even
  have hA_odd : Summable (fun k : ℕ => cotTerm z (2 * k + 1)) :=
    hA.comp_injective hinj_odd
  have hpow_even : ∀ k : ℕ, (-1 : ℂ) ^ ((2 * k) + 1) = -1 := by
    intro k
    rw [pow_succ, pow_mul]
    norm_num
  have hpow_odd : ∀ k : ℕ, (-1 : ℂ) ^ (((2 * k + 1)) + 1) = 1 := by
    intro k
    have hexp : ((2 * k + 1 : ℕ)) + 1 = 2 * (k + 1) := by ring
    rw [hexp, pow_mul]
    norm_num
  have hf_even_eq : (fun k : ℕ => (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k))
      = (fun k : ℕ => -(cotTerm z (2 * k))) := by
    funext k
    rw [hpow_even k]
    ring
  have hf_odd_eq : (fun k : ℕ => (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1))
      = (fun k : ℕ => cotTerm z (2 * k + 1)) := by
    funext k
    rw [hpow_odd k, one_mul]
  have hf_even : Summable (fun k : ℕ => (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k)) := by
    rw [hf_even_eq]
    exact hA_even.neg
  have hf_odd : Summable (fun k : ℕ => (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1)) := by
    rw [hf_odd_eq]
    exact hA_odd
  have hg : Summable (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n) :=
    Summable.even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      hf_even hf_odd
  have h2z : (2 : ℂ) * z ≠ 0 := mul_ne_zero (by norm_num) hz0
  have hfeq : (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      = (fun n : ℕ => (2 * z) * (((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))))) := by
    funext n
    exact catCotTerm_alt_eq z hz n
  have hf : Summable (fun n : ℕ => (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) := by
    have hdiv : Summable (fun n : ℕ => ((-1 : ℂ) ^ (n + 1) * cotTerm z n) / (2 * z)) :=
      hg.div_const (2 * z)
    have heq : (fun n : ℕ => ((-1 : ℂ) ^ (n + 1) * cotTerm z n) / (2 * z))
        = (fun n : ℕ => (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) := by
      funext n
      rw [catCotTerm_alt_eq z hz n]
      field_simp
    rw [heq] at hdiv
    exact hdiv
  have hmul : (∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      = (2 * z) * ∑' n : ℕ, ((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) := by
    rw [hfeq, tsum_mul_left]
  have htrans : (((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) - 1 / z)
      = (2 * z) * ∑' n : ℕ, ((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) :=
    hsub.trans (heven.trans hmul)
  have hdiv : ((((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) - 1 / z)
      / (2 * z))
      = ∑' n : ℕ, ((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) := by
    rw [htrans, mul_div_cancel_left₀ _ h2z]
  exact hdiv.symm

/-- Real cosecant partial fractions. -/
theorem catCsc_real_tsum (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∑' n : ℕ, ((-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2)))
      = ((Real.pi / Real.sin (Real.pi * (u / 2)) - 1 / (u / 2)) / (2 * (u / 2))) := by
  have hz0 : (0 : ℝ) < u / 2 := by linarith
  have hz1 : u / 2 < 1 := by linarith
  have hz : ((u / 2 : ℝ) : ℂ) ∈ Complex.integerComplement :=
    catMem_integerComplement (u / 2) hz0 hz1
  have hz2mem : (((u / 2 : ℝ) / 2 : ℝ) : ℂ) ∈ Complex.integerComplement := by
    apply catMem_integerComplement ((u / 2) / 2)
    · linarith
    · linarith
  have heq2 : (((u / 2 : ℝ) : ℂ) / 2) = ((((u / 2 : ℝ) / 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  have hz2 : ((u / 2 : ℝ) : ℂ) / 2 ∈ Complex.integerComplement := by
    rw [heq2]
    exact hz2mem
  have hz0' : ((u / 2 : ℝ) : ℂ) ≠ 0 := by
    have hne : (u / 2 : ℝ) ≠ 0 := ne_of_gt hz0
    exact_mod_cast hne
  have hcomplex := catCsc_tsum ((u / 2 : ℝ) : ℂ) hz hz2 hz0'
  have hLHS : (∑' n : ℕ, (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - ((u / 2 : ℝ) : ℂ) ^ 2)))
      = Complex.ofReal (∑' n : ℕ, (-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2))) := by
    have hterm : ∀ n : ℕ, (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - ((u / 2 : ℝ) : ℂ) ^ 2))
        = Complex.ofReal (((-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2)))) := by
      intro n
      push_cast
      ring
    calc (∑' n : ℕ, (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - ((u / 2 : ℝ) : ℂ) ^ 2)))
        = ∑' n : ℕ, Complex.ofReal (((-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2)))) :=
          tsum_congr hterm
      _ = Complex.ofReal (∑' n : ℕ, (-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2))) :=
          (RCLike.ofReal_tsum ℂ
            (fun n : ℕ => (-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2)))).symm
  have hRHS : ((((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * ((u / 2 : ℝ) : ℂ))
      - 1 / ((u / 2 : ℝ) : ℂ)) / (2 * ((u / 2 : ℝ) : ℂ)))
      = Complex.ofReal (((Real.pi / Real.sin (Real.pi * (u / 2)) - 1 / (u / 2))
        / (2 * (u / 2)))) := by
    push_cast
    ring
  rw [hLHS] at hcomplex
  rw [hRHS] at hcomplex
  exact Complex.ofReal_injective hcomplex

end MetaMathlibExt
end
