/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Def.Analysis.NormedSpace.RieszThorin


section

open MeasureTheory

namespace FunctionalAnalysis.RieszThorinWanted

lemma sgn_mul {κ : Type*} (y : κ → Complex) (i : κ) :
    y i * sgn y i = (‖y i‖ : ℂ) := by
  unfold sgn
  by_cases h : y i = 0
  · simp [h]
  · rw [ite_eq_right h]
    have hn : ‖y i‖ ≠ 0 := fun e => h (norm_eq_zero.mp e)
    have hC : ((‖y i‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_pow, pow_two, mul_div_cancel_left₀ _ hC]

lemma norm_sgn {κ : Type*} (y : κ → Complex) (i : κ) :
    ‖sgn y i‖ = if y i = 0 then 0 else 1 := by
  unfold sgn
  by_cases h : y i = 0
  · simp [h]
  · rw [ite_eq_right h, norm_div, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Complex.norm_nonneg _), ite_eq_right h]
    exact div_self (fun e => h (norm_eq_zero.mp e))

lemma dual_attain {κ : Type*} [Fintype κ]
    [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (y : κ → Complex) (hy : y ≠ 0)
    {q q' : ENNReal} (hq1 : 1 ≤ q) (hq : q⁻¹ + q'⁻¹ = 1) :
    ∃ g : κ → Complex, eLpNorm g q' Measure.count = 1 ∧
      ∑ k, y k * g k = ((eLpNorm y q Measure.count).toReal : ℂ) := by
  classical
  have hq0 : q ≠ 0 := ne_of_gt (one_pos.trans_le hq1)
  have hq'0 : q' ≠ 0 := q'_ne_zero_of_conj hq
  have hy0 : eLpNorm y q Measure.count ≠ 0 := by
    rw [Ne, eLpNorm_count_eq_zero_iff hq0]
    exact hy
  have hyTop : eLpNorm y q Measure.count ≠ ⊤ := eLpNorm_count_ne_top y hq0
  set A := (eLpNorm y q Measure.count).toReal with hA
  have hApos : 0 < A := ENNReal.toReal_pos hy0 hyTop
  obtain ⟨k₁, hk₁⟩ : ∃ k, y k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hy (funext fun k => hall k)
  rcases eq_or_ne q ⊤ with rfl | hqtop
  · have hq'inv1 : q'⁻¹ = 1 := by simpa using hq
    have hq'1 : q' = 1 := by
      have h2 := congrArg Inv.inv hq'inv1
      rwa [inv_inv, inv_one] at h2
    have hne : (Finset.univ : Finset κ).Nonempty := ⟨k₁, Finset.mem_univ k₁⟩
    obtain ⟨k₀, _, hk₀⟩ :=
      Finset.exists_max_image Finset.univ (fun k => ‖y k‖) hne
    have hk₀ne : y k₀ ≠ 0 := by
      intro h0
      apply hk₁
      have hle : ‖y k₁‖ ≤ ‖y k₀‖ := hk₀ k₁ (Finset.mem_univ k₁)
      rw [h0, norm_zero] at hle
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    have hsup : (⨆ i, ‖y i‖ₑ) = ‖y k₀‖ₑ :=
      le_antisymm (iSup_le fun i => by
        rw [enorm_complex_eq_ofReal, enorm_complex_eq_ofReal]
        exact ENNReal.ofReal_le_ofReal (hk₀ i (Finset.mem_univ i)))
        (le_iSup (fun i => ‖y i‖ₑ) k₀)
    have hAeq : A = ‖y k₀‖ := by
      rw [hA, eLpNorm_count_top_eq, hsup, enorm_complex_eq_ofReal,
        ENNReal.toReal_ofReal (Complex.norm_nonneg _)]
    refine ⟨fun k => if k = k₀ then sgn y k₀ else 0, ?_, ?_⟩
    · rw [hq'1, eLpNorm_count_one_eq, Finset.sum_eq_single k₀]
      · show ‖(if k₀ = k₀ then sgn y k₀ else 0 : Complex)‖ₑ = _
        rw [ite_eq_left rfl, enorm_complex_eq_ofReal, norm_sgn, ite_eq_right hk₀ne]
        simp
      · intro k _ hk
        rw [ite_eq_right hk]
        simp
      · intro h
        exact absurd (Finset.mem_univ k₀) h
    · rw [Finset.sum_eq_single k₀]
      · change y k₀ * (if k₀ = k₀ then sgn y k₀ else 0 : Complex) = _
        rw [ite_eq_left rfl, sgn_mul, hAeq]
      · intro k _ hk
        change y k * (if k = k₀ then sgn y k₀ else 0 : Complex) = _
        rw [ite_eq_right hk, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ k₀) h
  · have hq1r : 1 ≤ q.toReal := by
      have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
        hqtop).mpr hq1
      rwa [ENNReal.toReal_one] at h
    have hqpos : 0 < q.toReal := one_pos.trans_le hq1r
    have hqne0 : q.toReal ≠ 0 := ne_of_gt hqpos
    have hinner : (∑ k, ‖y k‖ₑ ^ q.toReal) =
        ENNReal.ofReal (∑ k, ‖y k‖ ^ q.toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ =>
        Real.rpow_nonneg (Complex.norm_nonneg _) _)]
      apply Finset.sum_congr rfl; intro k _
      rw [enorm_complex_eq_ofReal,
        ENNReal.ofReal_rpow_of_nonneg (Complex.norm_nonneg _)
          ENNReal.toReal_nonneg]
    have h1qnn : 0 ≤ 1 / q.toReal := le_of_lt (one_div_pos.mpr hqpos)
    have hSnn : 0 ≤ ∑ k, ‖y k‖ ^ q.toReal :=
      Finset.sum_nonneg fun k _ =>
        Real.rpow_nonneg (Complex.norm_nonneg _) _
    have hAeq : A = (∑ k, ‖y k‖ ^ q.toReal) ^ (1 / q.toReal) := by
      rw [hA, eLpNorm_count_eq_sum y hq0 hqtop, hinner,
        ENNReal.ofReal_rpow_of_nonneg hSnn h1qnn,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hSnn _)]
    have hS : ∑ k, ‖y k‖ ^ q.toReal = A ^ q.toReal := by
      have h1 : ((∑ k, ‖y k‖ ^ q.toReal) ^ (1 / q.toReal)) ^ q.toReal
          = (∑ k, ‖y k‖ ^ q.toReal) := by
        rw [← Real.rpow_mul hSnn, div_mul_cancel₀ 1 hqne0, Real.rpow_one]
      rw [← h1, hAeq]
    set e := q.toReal - 1 with he
    have he_nn : 0 ≤ e := by rw [he]; linarith [hq1r]
    have hAe : A ^ e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hApos e)
    set g : κ → Complex := fun k =>
      sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) with hg
    have hterm : ∀ k : κ, y k * g k =
        ((‖y k‖ * (‖y k‖ ^ e / A ^ e) : ℝ) : ℂ) := by
      intro k
      have : g k = sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) := rfl
      rw [this, ← mul_assoc, sgn_mul, Complex.ofReal_mul]
    have hpair : ∑ k, y k * g k = ((A : ℝ) : ℂ) := by
      have h1 : ∑ k, y k * g k =
          ((∑ k, ‖y k‖ * (‖y k‖ ^ e / A ^ e) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl; intro k _
        exact hterm k
      rw [h1]
      congr 1
      have hterm2 : ∀ k : κ, ‖y k‖ * (‖y k‖ ^ e / A ^ e) =
          ‖y k‖ ^ q.toReal / A ^ e := by
        intro k
        rw [← mul_div_assoc]
        congr 1
        rcases eq_or_lt_of_le (Complex.norm_nonneg (y k)) with h0 | hpos
        · rw [← h0, zero_mul, Real.zero_rpow hqne0]
        · have hqe1 : q.toReal = 1 + e := by rw [he]; ring
          rw [hqe1, Real.rpow_add hpos, Real.rpow_one]
      rw [Finset.sum_congr rfl (fun k _ => hterm2 k), ← Finset.sum_div, hS,
        ← Real.rpow_sub hApos]
      have hqe : q.toReal - e = 1 := by rw [he]; ring
      rw [hqe, Real.rpow_one]
    refine ⟨g, ?_, ?_⟩
    · rcases eq_or_ne q 1 with rfl | hq1ne
      · have hq'inv0 : q'⁻¹ = 0 := by simpa using hq
        have hq'top : q' = ⊤ := ENNReal.inv_eq_zero.mp hq'inv0
        have he0 : e = 0 := by
          rw [he, ENNReal.toReal_one, sub_self]
        have hg_eq : ∀ k, g k = sgn y k := by
          intro k
          have : g k = sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) := rfl
          rw [this, he0, Real.rpow_zero, Real.rpow_zero, div_one,
            Complex.ofReal_one, mul_one]
        rw [hq'top, eLpNorm_count_top_eq]
        apply le_antisymm
        · apply iSup_le; intro k
          rw [hg_eq k, enorm_complex_eq_ofReal, norm_sgn]
          by_cases hk : y k = 0 <;> simp [hk]
        · have h1 : ‖g k₁‖ₑ ≤ ⨆ i, ‖g i‖ₑ :=
            le_iSup (fun i => ‖g i‖ₑ) k₁
          rw [hg_eq k₁, enorm_complex_eq_ofReal, norm_sgn,
            ite_eq_right hk₁] at h1
          simpa using h1
      · have hsum : (q.toReal)⁻¹ + (q'.toReal)⁻¹ = 1 := by
          have h := congrArg ENNReal.toReal hq
          rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hq0)
            (ENNReal.inv_ne_top.mpr hq'0), ENNReal.toReal_inv,
            ENNReal.toReal_inv, ENNReal.toReal_one] at h
          exact h
        have hq'1 : 1 ≤ q' := q_ge_one_of_conj (by rw [add_comm]; exact hq)
        have hq'top : q' ≠ ⊤ := by
          rintro rfl
          simp only [ENNReal.inv_top, add_zero, ENNReal.inv_eq_one]at hq
          exact hq1ne hq
        have hq'1r : 1 ≤ q'.toReal := by
          have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
            hq'top).mpr hq'1
          rwa [ENNReal.toReal_one] at h
        have hq'pos : 0 < q'.toReal := one_pos.trans_le hq'1r
        have hqq' : e * q'.toReal = q.toReal := by
          have hq'ne0 : q'.toReal ≠ 0 := ne_of_gt hq'pos
          have h2 : q.toReal * q'.toReal = q.toReal + q'.toReal := by
            have h := hsum
            rw [inv_eq_one_div, inv_eq_one_div] at h
            field_simp at h
            linarith
          rw [he]
          linarith [h2]
        have htermN : ∀ k : κ, ‖g k‖ₑ ^ q'.toReal =
            ENNReal.ofReal (‖y k‖ ^ q.toReal / A ^ q.toReal) := by
          intro k
          have hnorm : ‖g k‖ =
              ‖sgn y k‖ * (‖y k‖ ^ e / A ^ e) := by
            have hgg : g k = sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) := rfl
            rw [hgg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (div_nonneg
                (Real.rpow_nonneg (Complex.norm_nonneg _) _)
                (le_of_lt (Real.rpow_pos_of_pos hApos _)))]
          by_cases hk : y k = 0
          · have hsgn0 : sgn y k = 0 := by unfold sgn; rw [ite_eq_left hk]
            have hg0 : g k = 0 := by
              have hgg : g k =
                sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) := rfl
              rw [hgg, hsgn0, zero_mul]
            have hyk0 : ‖y k‖ = 0 := norm_eq_zero.mpr hk
            rw [hg0, enorm_zero, ENNReal.zero_rpow_of_pos hq'pos,
              hyk0, Real.zero_rpow hqne0, zero_div, ENNReal.ofReal_zero]
          · have hsgn1 : ‖sgn y k‖ = 1 := by rw [norm_sgn, ite_eq_right hk]
            rw [enorm_complex_eq_ofReal, hnorm, hsgn1, one_mul,
              ENNReal.ofReal_rpow_of_nonneg
                (div_nonneg (Real.rpow_nonneg (Complex.norm_nonneg _) _)
                  (le_of_lt (Real.rpow_pos_of_pos hApos _)))
                ENNReal.toReal_nonneg,
              Real.div_rpow (Real.rpow_nonneg (Complex.norm_nonneg _) _)
                (le_of_lt (Real.rpow_pos_of_pos hApos _)),
              ← Real.rpow_mul (Complex.norm_nonneg (y k)),
              ← Real.rpow_mul (le_of_lt hApos), hqq']
        rw [eLpNorm_count_eq_sum g hq'0 hq'top]
        have hsumN : (∑ k, ‖g k‖ₑ ^ q'.toReal) =
            ENNReal.ofReal (∑ k, ‖y k‖ ^ q.toReal / A ^ q.toReal) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
          apply Finset.sum_congr rfl; intro k _
          exact htermN k
        rw [hsumN, ← Finset.sum_div, hS,
          div_self (ne_of_gt (Real.rpow_pos_of_pos hApos _)),
          ENNReal.ofReal_one, ENNReal.one_rpow]
    · rw [hpair, hA]

end FunctionalAnalysis.RieszThorinWanted
end
