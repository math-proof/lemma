import Mathlib
import sympy.Basic
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal


/--
[MeasureTheory_exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero.lean)
-/
@[path]
private lemma main
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {f : E → E}
  {a : E}
-- given
  (hf : ContDiffAt ℝ 1 f a)
  (hf' : (fderiv ℝ f a).det ≠ 0) :
-- imply
  ∃ s : Set E, IsOpen s ∧ a ∈ s ∧ Set.InjOn f s ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t ⊆ s, MeasurableSet t → ∀ g : E → ℝ≥0∞,
        (δ : ℝ≥0∞) * ∫⁻ x in t, g (f x) ∂μ ≤ ∫⁻ y in f '' t, g y ∂μ := by
-- proof
  classical
    obtain ⟨F', u, hu, hF'c, hF'⟩ := contDiffAt_one_iff.1 hf
    have hfa : HasFDerivAt f (F' a) a := hF' a (mem_of_mem_nhds hu)
    have hfd : fderiv ℝ f a = F' a := hfa.fderiv
    have hdet : (F' a).det ≠ 0 := by rwa [← hfd]
    set L : E ≃L[ℝ] E := (F' a).toContinuousLinearEquivOfDetNeZero hdet with hL
    have hLcoe : (L : E →L[ℝ] E) = F' a :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have hstrict : HasStrictFDerivAt f (L : E →L[ℝ] E) a := by
      rw [hLcoe]
      exact hf.hasStrictFDerivAt' hfa one_ne_zero
    set Φ := hstrict.toOpenPartialHomeomorph f with hΦ
    have hΦsrc : a ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
    have hΦcoe : (Φ : E → E) = f := rfl
    set d : ℝ := |(F' a).det| / 2 with hd_def
    have hdpos : 0 < d := half_pos (abs_pos.2 hdet)
    have hdlt : d < |(F' a).det| := half_lt_self (abs_pos.2 hdet)
    have hcont : ContinuousAt (fun x => |(F' x).det|) a :=
      ((continuous_abs.comp ContinuousLinearMap.continuous_det).continuousAt).comp
        (hF'c.continuousAt hu)
    have hev : ∀ᶠ x in 𝓝 a, x ∈ u ∧ d < |(F' x).det| ∧ x ∈ Φ.source := by
      filter_upwards [hu, hcont.eventually_const_lt hdlt, Φ.open_source.mem_nhds hΦsrc] with x h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨s, hsS, hso, has⟩ := mem_nhds_iff.1 hev
    have hinj : Set.InjOn f s := by
      intro x hx y hy hxy
      exact Φ.injOn (hsS hx).2.2 (hsS hy).2.2 hxy
    refine ⟨s, hso, has, hinj, Real.toNNReal d, Real.toNNReal_pos.2 hdpos, fun t hts ht g => ?_⟩
    have hderiv : ∀ x ∈ t, HasFDerivWithinAt f (F' x) t x := fun x hx =>
      (hF' x (hsS (hts hx)).1).hasFDerivWithinAt
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ht hderiv (hinj.mono hts) g,
      ENNReal.ofNNReal_toNNReal, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' ht fun x hx => ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hsS (hts hx)).2.1.le) le_rfl


-- created on 2026-10-23
