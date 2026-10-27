/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular


section

open MeasureTheory Complex

open scoped BigOperators

namespace Fourier.BochnerWanted

/-!
# Bochner's theorem on `ℝ`
-/

/-- Positive-definiteness sum equals the integral of a `normSq` (N1). -/
lemma charFun_posDef_sum_eq_integral_normSq
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ) :
    ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * charFun μ (x i - x j)
      = ((∫ y : ℝ, normSq (∑ j : Fin n, c j * cexp (↑(-(x j * y)) * I)) ∂μ : ℝ) : ℂ) := by
  have hexp_int : ∀ (t : ℝ), Integrable (fun y : ℝ => cexp (↑t * ↑y * I)) μ := by
    intro t
    apply Integrable.of_bound
      (C := 1)
    · exact ((Complex.continuous_exp.comp
        ((continuous_const.mul continuous_ofReal).mul continuous_const)).aestronglyMeasurable)
    · filter_upwards with y
      rw [show (↑t * ↑y * I : ℂ) = ↑(t * y) * I by push_cast; ring]
      rw [Complex.norm_exp_ofReal_mul_I]
  have hterm : ∀ (i j : Fin n),
      Integrable (fun y : ℝ => star (c i) * c j * cexp (↑(x i - x j) * ↑y * I)) μ := by
    intro i j
    exact (hexp_int (x i - x j)).const_mul _
  have hstep1 : ∀ (i j : Fin n),
      star (c i) * c j * charFun μ (x i - x j)
        = ∫ y : ℝ, star (c i) * c j * cexp (↑(x i - x j) * ↑y * I) ∂μ := by
    intro i j
    rw [charFun_apply_real]
    rw [MeasureTheory.integral_const_mul]
  have hinner : ∀ (i : Fin n),
      (∑ j : Fin n, ∫ y : ℝ, star (c i) * c j * cexp (↑(x i - x j) * ↑y * I) ∂μ)
        = ∫ y : ℝ, ∑ j : Fin n, star (c i) * c j * cexp (↑(x i - x j) * ↑y * I) ∂μ := by
    intro i
    exact (MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hterm i j)).symm
  have houter : (∑ i : Fin n, ∫ y : ℝ, ∑ j : Fin n,
        star (c i) * c j * cexp (↑(x i - x j) * ↑y * I) ∂μ)
        = ∫ y : ℝ, ∑ i : Fin n, ∑ j : Fin n,
          star (c i) * c j * cexp (↑(x i - x j) * ↑y * I) ∂μ := by
    exact (MeasureTheory.integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum _ (fun j _ => hterm i j))).symm
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hstep1 i j))]
  simp only [hinner]
  rw [houter, ← integral_complex_ofReal]
  congr 1
  funext y
  have hconj : ∀ (j : Fin n),
      star (c j * cexp (↑(-(x j * y)) * I)) = star (c j) * cexp (↑(x j * y) * I) := by
    intro j
    rw [star_mul, mul_comm]
    congr 1
    change (starRingEnd ℂ) (cexp (↑(-(x j * y)) * I)) = _
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal, Complex.conj_I]
  have hprod : (star (∑ j : Fin n, c j * cexp (↑(-(x j * y)) * I)))
      * (∑ j : Fin n, c j * cexp (↑(-(x j * y)) * I))
      = ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * cexp (↑(x i - x j) * ↑y * I) := by
    rw [star_sum]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hconj i]
    have hexp : cexp (↑(x i * y) * I) * cexp (↑(-(x j * y)) * I)
        = cexp (↑(x i - x j) * ↑y * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc (star (c i) * cexp (↑(x i * y) * I)) * (c j * cexp (↑(-(x j * y)) * I))
        = star (c i) * c j * (cexp (↑(x i * y) * I) * cexp (↑(-(x j * y)) * I)) := by ring
      _ = star (c i) * c j * cexp (↑(x i - x j) * ↑y * I) := by rw [hexp]
  have hnorm : (star (∑ j : Fin n, c j * cexp (↑(-(x j * y)) * I)))
      * (∑ j : Fin n, c j * cexp (↑(-(x j * y)) * I))
      = ((normSq (∑ j : Fin n, c j * cexp (↑(-(x j * y)) * I)) : ℝ) : ℂ) := by
    have h := Complex.mul_conj (∑ j : Fin n, c j * cexp (↑(-(x j * y)) * I))
    rw [mul_comm] at h
    exact h
  rw [← hprod, hnorm]

/-- Reverse direction of Bochner (N2): every characteristic function is continuous, 1 at 0,
positive-definite. -/
lemma bochner_mpr
    {f : ℝ → ℂ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hf : ∀ (t : ℝ), f t = charFun μ t) :
    Continuous f ∧ f 0 = 1 ∧
      ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
        let S := ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j)
        S.im = 0 ∧ 0 ≤ S.re := by
  have hfeq : f = charFun μ := funext hf
  refine ⟨?_, ?_, ?_⟩
  · rw [hfeq]
    exact continuous_charFun
  · rw [hf 0, charFun_zero, probReal_univ, Complex.ofReal_one]
  · intro n x c
    dsimp only
    have hsum : (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j))
        = ((∫ y : ℝ, normSq (∑ j : Fin n, c j * cexp (↑(-(x j * y)) * I)) ∂μ : ℝ) : ℂ) := by
      simp only [hf]
      exact charFun_posDef_sum_eq_integral_normSq μ n x c
    rw [hsum, Complex.ofReal_im]
    refine ⟨rfl, ?_⟩
    rw [Complex.ofReal_re]
    apply integral_nonneg
    intro y
    exact normSq_nonneg _

end Fourier.BochnerWanted
end
