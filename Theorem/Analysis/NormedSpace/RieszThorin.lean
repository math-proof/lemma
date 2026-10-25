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


section

open MeasureTheory

namespace FunctionalAnalysis.RieszThorinWanted

lemma holder_conj {q : ENNReal} (hq : 1 ≤ q) :
    ∃ q' : ENNReal, q⁻¹ + q'⁻¹ = 1 := by
  refine ⟨(1 - q⁻¹)⁻¹, ?_⟩
  rw [inv_inv]
  have hle : q⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hq
  exact add_tsub_cancel_of_le hle

lemma eLpNorm_count_eq_zero_iff {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {r : ENNReal} (hr : r ≠ 0) (y : α → Complex) :
    eLpNorm y r Measure.count = 0 ↔ y = 0 := by
  have := Fintype.ofFinite α
  rw [eLpNorm_eq_zero_iff hr]
  constructor
  · intro h; funext i; exact Measure.ae_count_iff.mp h i
  · intro h; exact Measure.ae_count_iff.mpr (fun i => by simp [h])

lemma enorm_complex_eq_ofReal (z : Complex) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← coe_nnnorm z, ENNReal.ofReal_coe_nnreal]

lemma aemeas_count {α : Type*} [MeasurableSpace α] (y : α → Complex)
    [Finite α] [MeasurableSingletonClass α] :
    AEStronglyMeasurable y Measure.count :=
  (measurable_of_finite y).aestronglyMeasurable

lemma eLpNorm_count_ne_top {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (y : α → Complex) {r : ENNReal} (hr : r ≠ 0) :
    eLpNorm y r Measure.count ≠ ⊤ := by
  have := Fintype.ofFinite α
  have hlt : eLpNorm y r Measure.count < ⊤ := by
    rw [eLpNorm_count_lt_top hr]
    intro i
    exact lt_top_iff_ne_top.mpr enorm_ne_top
  exact ne_of_lt hlt

lemma eLpNorm_count_eq_sum {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (y : α → Complex) {r : ENNReal}
    (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    eLpNorm y r Measure.count = (∑ i, ‖y i‖ₑ ^ r.toReal) ^ (1 / r.toReal) := by
  have hmeas : AEStronglyMeasurable y Measure.count := aemeas_count y
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt hmeas, lintegral_count,
    tsum_fintype]

lemma eLpNorm_count_one_eq {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (y : α → Complex) :
    eLpNorm y 1 Measure.count = ∑ i, ‖y i‖ₑ := by
  have hmeas : AEStronglyMeasurable y Measure.count := aemeas_count y
  rw [eLpNorm_one_eq_lintegral_enorm hmeas, lintegral_count, tsum_fintype]

lemma eLpNorm_count_top_eq {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (y : α → Complex) :
    eLpNorm y ⊤ Measure.count = ⨆ i, ‖y i‖ₑ := by
  have := Fintype.ofFinite α
  have hmeas : AEStronglyMeasurable y Measure.count := aemeas_count y
  rw [eLpNorm_exponent_top hmeas, eLpNormEssSup_count]

lemma q_ge_one_of_conj {q q' : ENNReal} (hq : q⁻¹ + q'⁻¹ = 1) :
    1 ≤ q := by
  have h : q⁻¹ ≤ q⁻¹ + q'⁻¹ := le_add_right le_rfl
  rw [hq] at h
  exact ENNReal.inv_le_one.mp h

lemma q'_ne_zero_of_conj {q q' : ENNReal} (hq : q⁻¹ + q'⁻¹ = 1) :
    q' ≠ 0 := by
  rintro rfl
  rw [ENNReal.inv_zero, add_top] at hq
  exact (by simp : (⊤ : ENNReal) ≠ 1) hq

lemma pairing_le {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (y g : κ → Complex) {q q' : ENNReal}
    (hq : q⁻¹ + q'⁻¹ = 1) :
    ‖∑ k, y k * g k‖ₑ ≤
      eLpNorm y q Measure.count * eLpNorm g q' Measure.count := by
  have hq1 : 1 ≤ q := q_ge_one_of_conj hq
  have hq'0 : q' ≠ 0 := q'_ne_zero_of_conj hq
  have hq0 : q ≠ 0 := ne_of_gt (one_pos.trans_le hq1)
  calc ‖∑ k, y k * g k‖ₑ ≤ ∑ k, ‖y k‖ₑ * ‖g k‖ₑ := by
        calc ‖∑ k, y k * g k‖ₑ ≤ ∑ k, ‖y k * g k‖ₑ :=
              enorm_sum_le Finset.univ _
          _ = ∑ k, ‖y k‖ₑ * ‖g k‖ₑ := by
              apply Finset.sum_congr rfl; intro k _
              exact enorm_mul _ _
    _ ≤ eLpNorm y q Measure.count * eLpNorm g q' Measure.count := by
        rcases eq_or_ne q 1 with rfl | hq1ne
        · rw [eLpNorm_count_one_eq, Finset.sum_mul]
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_right (enorm_le_eLpNorm_count g i hq'0) _
        · rcases eq_or_ne q ⊤ with rfl | hqtop
          · have hq'inv1 : q'⁻¹ = 1 := by simpa using hq
            have hq'1 : q' = 1 := by
              have h2 := congrArg Inv.inv hq'inv1
              rwa [inv_inv, inv_one] at h2
            rw [hq'1, eLpNorm_count_top_eq, eLpNorm_count_one_eq, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_left (le_iSup (fun j => ‖y j‖ₑ) i) _
          · have hq1lt : 1 < q := lt_of_le_of_ne hq1 (Ne.symm hq1ne)
            have h1r : 1 < q.toReal := by
              have h := (ENNReal.toReal_lt_toReal (by simp : (1 : ENNReal) ≠ ⊤) hqtop).mpr hq1lt
              rwa [ENNReal.toReal_one] at h
            have hsum : (q.toReal)⁻¹ + (q'.toReal)⁻¹ = 1 := by
              have h := congrArg ENNReal.toReal hq
              rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hq0)
                (ENNReal.inv_ne_top.mpr hq'0), ENNReal.toReal_inv,
                ENNReal.toReal_inv, ENNReal.toReal_one] at h
              exact h
            have hq'top : q' ≠ ⊤ := by
              rintro rfl
              rw [ENNReal.toReal_top, inv_zero, add_zero] at hsum
              have h1 : q.toReal = 1 := by
                have h2 := congrArg Inv.inv hsum
                rwa [inv_inv, inv_one] at h2
              linarith
            have hconj : q.toReal.HolderConjugate q'.toReal := by
              rw [Real.holderConjugate_iff]
              exact ⟨h1r, hsum⟩
            have hH := ENNReal.inner_le_Lp_mul_Lq Finset.univ
              (fun i => ‖y i‖ₑ) (fun i => ‖g i‖ₑ) hconj
            rw [eLpNorm_count_eq_sum y hq0 hqtop,
              eLpNorm_count_eq_sum g hq'0 hq'top]
            simpa using hH

end FunctionalAnalysis.RieszThorinWanted
end
