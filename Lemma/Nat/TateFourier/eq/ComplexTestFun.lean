import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.LanglandsTunnell.ArchPlace
import Lemma.Int.P2MUtil

open MeasureTheory Complex LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped Real RealInnerProductSpace ENNReal

/--
[LanglandsTunnell_ArchPlace_tateFourier_complexTestFun_zero_self](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_ArchPlace_tateFourier_complexTestFun_zero_self.lean)
-/

private lemma psiComplex_mul_eq_exp_inner (z w : ℂ) :
  psiComplex (z * w) = Complex.exp ((-(4 * (π : ℂ) * Complex.I)) * ((⟪(starRingEnd ℂ) w, z⟫ : ℝ) : ℂ)) := by
  rw [psiComplex_apply]
  congr 1
  have h1 : ⟪(starRingEnd ℂ) w, z⟫ = (z * w).re := by
    rw [Complex.inner, Complex.conj_conj]
  have h2 : (z * w) + (starRingEnd ℂ) (z * w) = ((2 * (z * w).re : ℝ) : ℂ) :=
    Complex.add_conj (z * w)
  rw [h1, h2]
  push_cast
  ring

private lemma  tateFourier_psiComplex_complexTestFun_zero_impl :
  tateFourier psiComplex ((2 : ℝ≥0∞) • volume) (complexTestFun 0) = complexTestFun 0 := by
  funext w
  rw [tateFourier, integral_smul_measure]
  have hker : ∀ z : ℂ, complexTestFun 0 z * psiComplex (z * w) = Complex.exp (-(2 * (π : ℂ)) * ‖z‖ ^ 2
          + (-(4 * (π : ℂ) * Complex.I)) * ((⟪(starRingEnd ℂ) w, z⟫ : ℝ) : ℂ)) := by
    intro z
    rw [complexTestFun_zero_apply, psiComplex_mul_eq_exp_inner, ← Complex.exp_add]
    congr 1
    ring
  simp_rw [hker]
  have hb : (0 : ℝ) < ((2 : ℂ) * (π : ℂ)).re := by
    simp [Real.pi_pos]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb
    (-(4 * (π : ℂ) * Complex.I)) ((starRingEnd ℂ) w)]
  rw [complexTestFun_zero_apply]
  have hnc : ‖(starRingEnd ℂ) w‖ = ‖w‖ := norm_conj w
  rw [hnc]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfr : ((Module.finrank ℝ ℂ : ℂ) / 2) = 1 := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hfr, Complex.cpow_one]
  have hexp : (-(4 * (π : ℂ) * Complex.I)) ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * (2 * (π : ℂ))) = -(2 * (π : ℂ) * (‖w‖ : ℂ) ^ 2) := by
    have h4 : (-(4 * (π : ℂ) * Complex.I)) ^ 2 = -(16 * (π : ℂ) ^ 2) := by
      rw [neg_pow, mul_pow, mul_pow, Complex.I_sq]
      ring
    rw [h4]
    field_simp
    ring
  rw [hexp]
  rw [ENNReal.toReal_ofNat, real_smul]
  push_cast
  field_simp
@[path]
private lemma main
  :
-- imply
  tateFourier psiComplex ((2 : ℝ≥0∞) • volume) (complexTestFun 0) = complexTestFun 0 :=
-- proof
  tateFourier_psiComplex_complexTestFun_zero_impl


-- created on 2026-10-23
