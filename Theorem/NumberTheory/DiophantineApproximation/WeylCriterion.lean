/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/WeylCriterion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Weyl's equidistribution criterion: a real sequence is equidistributed modulo 1
if and only if every nontrivial Fourier mean vanishes.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Def.NumberTheory.DiophantineApproximation.WeylCriterion
open scoped BigOperators
open Filter Topology


namespace MetaMathlibExt

lemma wcPhi_cont (a b δ : ℝ) : Continuous (wcPhi a b δ) := by
  have h1 : Continuous (fun t : ℝ => (t - a) / δ) :=
    (continuous_id.sub continuous_const).div_const δ
  have h2 : Continuous (fun t : ℝ => (b - t) / δ) :=
    (continuous_const.sub continuous_id).div_const δ
  unfold wcPhi
  exact continuous_const.max (continuous_const.min (h1.min h2))

lemma wcPhi_eq_zero_of_le (a b δ t : ℝ) (hδ : 0 < δ) (ht : t ≤ a) :
    wcPhi a b δ t = 0 := by
  unfold wcPhi
  have h1 : (t - a) / δ ≤ 0 := by
    rw [div_le_iff₀ hδ, zero_mul]
    exact sub_nonpos.mpr ht
  have h2 : min 1 (min ((t - a) / δ) ((b - t) / δ)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h1)
  exact max_eq_left h2

lemma wcPhi_eq_zero_of_ge (a b δ t : ℝ) (hδ : 0 < δ) (ht : b ≤ t) :
    wcPhi a b δ t = 0 := by
  unfold wcPhi
  have h1 : (b - t) / δ ≤ 0 := by
    rw [div_le_iff₀ hδ, zero_mul]
    exact sub_nonpos.mpr ht
  have h2 : min 1 (min ((t - a) / δ) ((b - t) / δ)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h1)
  exact max_eq_left h2

/-- The bump sum is bounded by the interval count. -/
lemma wcPhi_sum_le (x : ℕ → ℝ) (a b δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∑ n ∈ Finset.range N, wcPhi a b δ (Int.fract (x n)) ≤
      (wcCnt x a b N : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
    (fun n => wcPhi a b δ (Int.fract (x n)))
  have h1 : ∑ n ∈ Finset.filter
      (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b) (Finset.range N),
      wcPhi a b δ (Int.fract (x n)) ≤ (wcCnt x a b N : ℝ) := by
    calc ∑ n ∈ Finset.filter
            (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
            (Finset.range N),
            wcPhi a b δ (Int.fract (x n))
        ≤ ∑ _n ∈ Finset.filter
            (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
            (Finset.range N), (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => wcPhi_le_one _ _ _ _
      _ = (wcCnt x a b N : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, wcCnt]
  have hzero : ∑ n ∈ Finset.filter
      (fun n => ¬(a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)) (Finset.range N),
      wcPhi a b δ (Int.fract (x n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    rcases lt_or_ge (Int.fract (x n)) a with ha | ha
    · exact wcPhi_eq_zero_of_le a b δ _ hδ (le_of_lt ha)
    · have hb : b ≤ Int.fract (x n) := by
        by_contra hcon
        exact hn.2 ⟨ha, not_le.mp hcon⟩
      exact wcPhi_eq_zero_of_ge a b δ _ hδ hb
  rw [← hsplit, hzero, add_zero]
  exact h1

lemma wcPhi_integral_ge (a b δ : ℝ) (ha0 : 0 ≤ a) (_hab : a < b)
    (hb1 : b ≤ 1) (hδ : 0 < δ) (h2 : 2 * δ < b - a) :
    b - a - 2 * δ ≤ ∫ t in (0 : ℝ)..1, wcPhi a b δ t := by
  classical
  have huv : a + δ ≤ b - δ := by linarith
  have h0u : (0 : ℝ) ≤ a + δ := by linarith [ha0, le_of_lt hδ]
  have hv1 : b - δ ≤ 1 := by linarith [hb1, le_of_lt hδ]
  have hcont : Continuous (wcPhi a b δ) := wcPhi_cont _ _ _
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    ((hcont.intervalIntegrable (μ := MeasureTheory.volume)) 0 (a + δ))
    ((hcont.intervalIntegrable (μ := MeasureTheory.volume)) (a + δ) (b - δ))
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    ((hcont.intervalIntegrable (μ := MeasureTheory.volume)) 0 (b - δ))
    ((hcont.intervalIntegrable (μ := MeasureTheory.volume)) (b - δ) 1)
  have houter1 : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..(a + δ), wcPhi a b δ t := by
    have h := intervalIntegral.integral_mono_on h0u
      ((continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 (a + δ)) :
        IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume 0 (a + δ))
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (a + δ))
      (fun t _ => wcPhi_nonneg a b δ t)
    have h0 : (∫ t in (0 : ℝ)..(a + δ), (fun _ : ℝ => (0 : ℝ)) t) = 0 := by
      simp only [intervalIntegral.integral_zero]
    rwa [h0] at h
  have houter2 : (0 : ℝ) ≤ ∫ t in (b - δ)..(1 : ℝ), wcPhi a b δ t := by
    have h := intervalIntegral.integral_mono_on hv1
      ((continuous_const.intervalIntegrable (μ := MeasureTheory.volume) (b - δ) 1) :
        IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume (b - δ) 1)
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) (b - δ) 1)
      (fun t _ => wcPhi_nonneg a b δ t)
    have h0 : (∫ t in (b - δ)..(1 : ℝ), (fun _ : ℝ => (0 : ℝ)) t) = 0 := by
      simp only [intervalIntegral.integral_zero]
    rwa [h0] at h
  have hmid : (b - δ) - (a + δ) ≤
      ∫ t in (a + δ)..(b - δ), wcPhi a b δ t := by
    have h := intervalIntegral.integral_mono_on huv
      ((continuous_const.intervalIntegrable (μ := MeasureTheory.volume) (a + δ) (b - δ)) :
        IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume (a + δ)
          (b - δ))
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) (a + δ) (b - δ))
      (fun t ht => by
        rw [Set.mem_Icc] at ht
        exact le_of_eq
          (wcPhi_eq_one a b δ t hδ ht.1 ht.2).symm)
    have h1 : (∫ t in (a + δ)..(b - δ), (fun _ : ℝ => (1 : ℝ)) t) =
        (b - δ) - (a + δ) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rwa [h1] at h
  have hfinal : b - a - 2 * δ = ((b - δ) - (a + δ)) := by ring
  rw [hfinal]
  linarith [e1, e2, houter1, hmid, houter2]

end MetaMathlibExt
