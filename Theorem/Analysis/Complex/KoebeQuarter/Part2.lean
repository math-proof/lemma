/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.Complex.KoebeQuarter
/-!
# Koebe one-quarter theorem
-/


section

namespace Complex.KoebeQuarterWanted

open MeasureTheory

theorem koebe_lintegral_annulus_polar
    (g : ℂ → ENNReal) (ρ r : ℝ)
    (hg : Measurable g)
    (hρ0 : 0 ≤ ρ) :
    ∫⁻ z in koebeAnnulus ρ r, g z =
      ∫⁻ t in Set.Ioo ρ r,
        ENNReal.ofReal t * ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          g (circleMap 0 t θ) := by
  have hopen : IsOpen (koebeAnnulus ρ r) := by
    change IsOpen {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < r}
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hAmeas : MeasurableSet (koebeAnnulus ρ r) := hopen.measurableSet
  have hsymm_cont : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    have e : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
        = (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) *
          (((Real.cos p.2 : ℝ) : ℂ) +
            ((Real.sin p.2 : ℝ) : ℂ) * Complex.I)) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [e]
    fun_prop
  have hAE : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
        (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm p))
      ((volume.prod volume).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)) :=
    (((ENNReal.measurable_ofReal.comp measurable_fst).smul
      ((hg.indicator hAmeas).comp hsymm_cont.measurable))).aemeasurable
  have hmem_iff : ∀ t' : ℝ, ∀ θ : ℝ, 0 < t' →
      (Complex.polarCoord.symm (t', θ) ∈ koebeAnnulus ρ r ↔
        t' ∈ Set.Ioo ρ r) := by
    intro t' θ ht'
    have h1 : ‖Complex.polarCoord.symm (t', θ)‖ = t' := by
      rw [Complex.norm_polarCoord_symm]
      change |t'| = t'
      exact abs_of_pos ht'
    unfold koebeAnnulus
    rw [Set.mem_ofPred_eq, h1]
    rfl
  have hsymm_circ : ∀ t' : ℝ, ∀ θ : ℝ,
      Complex.polarCoord.symm (t', θ) = circleMap 0 t' θ := by
    intro t' θ
    rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  have hsub2 : Set.Ioo ρ r ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    change (0 : ℝ) < t
    exact lt_of_le_of_lt hρ0 ht.1
  have hinner : ∀ t' : ℝ, t' ∈ Set.Ioi (0 : ℝ) →
      (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal t' *
          (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm (t', θ)))
      = (Set.Ioo ρ r).indicator
        (fun t => ENNReal.ofReal t *
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap 0 t θ)) t' := by
    intro t' ht'
    have ht'pos : 0 < t' := ht'
    have hgc : Measurable (fun θ : ℝ => g (circleMap 0 t' θ)) :=
      hg.comp (continuous_circleMap 0 t').measurable
    by_cases htr : t' ∈ Set.Ioo ρ r
    · have heq : Set.EqOn
          (fun θ => ENNReal.ofReal t' *
            (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm (t', θ)))
          (fun θ => ENNReal.ofReal t' * g (circleMap 0 t' θ))
          (Set.Ioo (-Real.pi) Real.pi) := by
        intro θ _
        have hmemA : Complex.polarCoord.symm (t', θ) ∈ koebeAnnulus ρ r :=
          (hmem_iff t' θ ht'pos).mpr htr
        change ENNReal.ofReal t' *
            (koebeAnnulus ρ r).indicator g
              (Complex.polarCoord.symm (t', θ)) =
            ENNReal.ofReal t' * g (circleMap 0 t' θ)
        rw [Set.indicator_of_mem hmemA, hsymm_circ]
      rw [Set.indicator_of_mem htr,
        setLIntegral_congr_fun measurableSet_Ioo heq,
        lintegral_const_mul _ hgc]
    · have heq0 : Set.EqOn
          (fun θ => ENNReal.ofReal t' *
            (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm (t', θ)))
          (fun _ => 0) (Set.Ioo (-Real.pi) Real.pi) := by
        intro θ _
        have hmemA : Complex.polarCoord.symm (t', θ) ∉ koebeAnnulus ρ r := by
          intro hc
          exact htr ((hmem_iff t' θ ht'pos).mp hc)
        change ENNReal.ofReal t' *
            (koebeAnnulus ρ r).indicator g
              (Complex.polarCoord.symm (t', θ)) = 0
        rw [Set.indicator_of_notMem hmemA, mul_zero]
      rw [Set.indicator_of_notMem htr,
        setLIntegral_congr_fun measurableSet_Ioo heq0]
      exact lintegral_zero
  have houter : Set.EqOn
      (fun t' : ℝ => ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal t' *
          (koebeAnnulus ρ r).indicator g (Complex.polarCoord.symm (t', θ)))
      (fun t' : ℝ => (Set.Ioo ρ r).indicator
        (fun t => ENNReal.ofReal t *
          ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, g (circleMap 0 t θ)) t')
      (Set.Ioi (0 : ℝ)) :=
    fun t' ht' => hinner t' ht'
  rw [← lintegral_indicator hAmeas, ← Complex.lintegral_comp_polarCoord_symm]
  rw [polarCoord_target, Measure.volume_eq_prod]
  rw [setLIntegral_prod _ hAE]
  simp only [smul_eq_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi houter,
    ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr_ae
  filter_upwards with t
  by_cases htI : t ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem htI]
  · rw [Set.indicator_of_notMem htI]
    have htr : t ∉ Set.Ioo ρ r := fun hc => htI (hsub2 hc)
    rw [Set.indicator_of_notMem htr]

theorem koebe_lintegral_Ioo_eq
    (F : ℝ → ℝ) (hcont : ContinuousOn F (Set.uIcc (-Real.pi) Real.pi))
    (hper : Function.Periodic F (2 * Real.pi))
    (hnn : ∀ θ : ℝ, 0 ≤ F θ) :
    (∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F θ))
      = ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * Real.pi), F θ) := by
  have hle : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  have hint : IntervalIntegrable F volume (-Real.pi) Real.pi :=
    hcont.intervalIntegrable
  have hIoo : IntegrableOn F (Set.Ioo (-Real.pi) Real.pi) volume :=
    IntegrableOn.congr_set_ae
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hint)
      Ioo_ae_eq_Ioc
  have hnn' : 0 ≤ᵐ[volume.restrict (Set.Ioo (-Real.pi) Real.pi)] F :=
    Filter.Eventually.of_forall hnn
  have e1 : ENNReal.ofReal (∫ θ in Set.Ioo (-Real.pi) Real.pi, F θ)
      = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F θ) :=
    ofReal_integral_eq_lintegral_ofReal hIoo hnn'
  rw [← e1]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hle]
  have h := hper.intervalIntegral_add_eq (-Real.pi) 0
  rwa [show (-Real.pi) + 2 * Real.pi = Real.pi by ring,
    show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring] at h

theorem koebe_area_lower
    (G m : ℂ → ℂ) (c : ℂ) (ρ r : ℝ)
    (hρ0 : 0 < ρ) (hρr : ρ < r) (hr1 : r < 1)
    (hG' : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
      HasDerivAt G (-(((z ^ 2))⁻¹) + m z) z)
    (hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}))
    (hm : DifferentiableOn ℂ m (Metric.ball (0 : ℂ) 1))
    (hm0 : m 0 = c)
    (hmeas : Measurable
      (fun z : ℂ => ENNReal.ofReal (‖-(((z ^ 2))⁻¹) + m z‖ ^ 2))) :
    ENNReal.ofReal
        (Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2))
      ≤ volume (G '' koebeAnnulus ρ r) := by
  have hρr' : ρ ≤ r := le_of_lt hρr
  have hAsub : koebeAnnulus ρ r ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    have hball : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hne : z ∉ ({0} : Set ℂ) := by
      rw [Set.mem_singleton_iff]
      intro hcon
      rw [hcon, norm_zero] at h1
      linarith
    exact ⟨hball, hne⟩
  have hAmeas : MeasurableSet (koebeAnnulus ρ r) := by
    have hopen : IsOpen (koebeAnnulus ρ r) := by
      change IsOpen {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < r}
      exact (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    exact hopen.measurableSet
  have hG'A : ∀ z ∈ koebeAnnulus ρ r,
      HasDerivAt G (-(((z ^ 2))⁻¹) + m z) z := by
    intro z hz
    obtain ⟨hb, hn⟩ := hAsub hz
    have hne : z ≠ 0 := fun h => hn (Set.mem_singleton_iff.mpr h)
    exact hG' z hb hne
  have hGinjA : Set.InjOn G (koebeAnnulus ρ r) := hGinj.mono hAsub
  have hvol := vol_image_eq_lintegral_norm_deriv_sq (koebeAnnulus ρ r) G
    (fun z => -(((z ^ 2))⁻¹) + m z) hAmeas hG'A hGinjA
  have hpolar := koebe_lintegral_annulus_polar
    (fun z => ENNReal.ofReal (‖-(((z ^ 2))⁻¹) + m z‖ ^ 2)) ρ r hmeas
    (le_of_lt hρ0)
  have hinner_lb : ∀ t ∈ Set.Ioo ρ r,
      ENNReal.ofReal (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))
      ≤ ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal
          (‖-((((circleMap 0 t θ) ^ 2))⁻¹) + m (circleMap 0 t θ)‖ ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hρ0 ht.1
    have ht1 : t < 1 := lt_trans ht.2 hr1
    have htne : t ≠ 0 := ne_of_gt ht0
    have hnorm_t : ∀ θ : ℝ, ‖circleMap 0 t θ‖ = t := by
      intro θ
      rw [norm_circleMap_zero, abs_of_pos ht0]
    have hmw_cont : ContinuousOn (fun θ : ℝ => m (circleMap 0 t θ))
        (Set.uIcc (-Real.pi) Real.pi) := by
      have hmaps : Set.MapsTo (circleMap 0 t) (Set.uIcc (-Real.pi) Real.pi)
          (Metric.ball (0 : ℂ) 1) := by
        intro θ _
        rw [Metric.mem_ball, dist_zero_right, hnorm_t θ]
        exact ht1
      have h := (hm.continuousOn).comp
        (continuous_circleMap 0 t).continuousOn hmaps
      exact h.congr (fun θ _ => rfl)
    have hsqc : ContinuousOn (fun θ : ℝ => (circleMap 0 t θ) ^ 2)
        (Set.uIcc (-Real.pi) Real.pi) :=
      ((continuous_circleMap 0 t).continuousOn.mul
        (continuous_circleMap 0 t).continuousOn).congr
        (fun θ _ => pow_two _)
    have hAc : ContinuousOn (fun θ : ℝ => -(((circleMap 0 t θ) ^ 2))⁻¹)
        (Set.uIcc (-Real.pi) Real.pi) := by
      have hne : ∀ θ ∈ Set.uIcc (-Real.pi) Real.pi,
          ((circleMap 0 t θ) ^ 2) ≠ 0 := by
        intro θ _
        have h0' : circleMap 0 t θ ≠ 0 := by
          intro hcon
          apply htne
          rw [← hnorm_t θ, hcon, norm_zero]
        exact pow_ne_zero 2 h0'
      have h := hsqc.inv₀ hne
      have h2 := h.neg
      exact h2.congr (fun θ _ => rfl)
    have hcont : ContinuousOn
        (fun θ => ‖-((((circleMap 0 t θ) ^ 2))⁻¹) + m (circleMap 0 t θ)‖ ^ 2)
        (Set.uIcc (-Real.pi) Real.pi) := by
      have hsumc : ContinuousOn
          (fun θ : ℝ => -(((circleMap 0 t θ) ^ 2))⁻¹ + m (circleMap 0 t θ))
          (Set.uIcc (-Real.pi) Real.pi) :=
        (hAc.add hmw_cont).congr (fun θ _ => rfl)
      have h := (hsumc.norm).mul (hsumc.norm)
      exact h.congr (fun θ _ => pow_two _)
    have hper : Function.Periodic
        (fun θ => ‖-((((circleMap 0 t θ) ^ 2))⁻¹) + m (circleMap 0 t θ)‖ ^ 2)
        (2 * Real.pi) := by
      intro θ
      simp only []
      rw [periodic_circleMap 0 t θ]
    rw [koebe_lintegral_Ioo_eq _ hcont hper (fun θ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (koebe_circle_integral_lower m c t hm hm0 ht0 ht1)
  have hmono : (∫⁻ t in Set.Ioo ρ r,
      ENNReal.ofReal t * ENNReal.ofReal (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
      ≤ ∫⁻ t in Set.Ioo ρ r,
        ENNReal.ofReal t * ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal
            (‖-((((circleMap 0 t θ) ^ 2))⁻¹) + m (circleMap 0 t θ)‖ ^ 2) := by
    rw [← lintegral_indicator measurableSet_Ioo,
      ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_mono
    intro t
    by_cases ht : t ∈ Set.Ioo ρ r
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact mul_le_mul_of_nonneg_left (hinner_lb t ht) (by positivity)
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  have hradial : (∫⁻ t in Set.Ioo ρ r,
      ENNReal.ofReal t * ENNReal.ofReal (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
      = ENNReal.ofReal
        (Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) +
          Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)) := by
    have e_rw : ∀ t ∈ Set.Ioo ρ r, ENNReal.ofReal t *
        ENNReal.ofReal (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))
        = ENNReal.ofReal (t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))) := by
      intro t ht
      rw [← ENNReal.ofReal_mul (le_of_lt (lt_trans hρ0 ht.1))]
    rw [setLIntegral_congr_fun measurableSet_Ioo e_rw]
    have hFcont : ContinuousOn
        (fun t : ℝ => t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
        (Set.uIcc ρ r) := by
      have hne : ∀ t ∈ Set.uIcc ρ r, t ≠ 0 := by
        intro t ht
        rw [Set.uIcc_of_le hρr'] at ht
        rw [Set.mem_Icc] at ht
        exact ne_of_gt (lt_of_lt_of_le hρ0 ht.1)
      have hbase : ContinuousOn (fun t : ℝ => t) (Set.uIcc ρ r) :=
        continuous_id.continuousOn
      have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc ρ r) :=
        (hbase.inv₀ hne).congr (fun t _ => rfl)
      have hpow : ContinuousOn (fun t : ℝ => (t⁻¹) ^ 4) (Set.uIcc ρ r) :=
        (hinv.pow 4).congr (fun t _ => rfl)
      have hinner : ContinuousOn
          (fun t : ℝ => 2 * Real.pi * ((t⁻¹) ^ 4 + ‖c‖ ^ 2))
          (Set.uIcc ρ r) :=
        (hpow.add_const _).const_mul _
      exact hbase.mul hinner
    have hInt : IntervalIntegrable
        (fun t : ℝ => t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
        volume ρ r := hFcont.intervalIntegrable
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo ρ r)]
        (fun t : ℝ => t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0' : 0 ≤ t := le_of_lt (lt_trans hρ0 ht.1)
      have h1 : (0 : ℝ) ≤ 2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2) := by positivity
      exact mul_nonneg ht0' h1
    have hB : (∫ t in Set.Ioo ρ r, t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
        = Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) +
          Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2) := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hρr']
      have hΦ : ∀ t ∈ Set.uIcc ρ r,
          HasDerivAt (fun t : ℝ => -Real.pi * (t⁻¹) ^ 2 + Real.pi * ‖c‖ ^ 2 * t ^ 2)
            (t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2))) t := by
        intro t ht
        have htpos : 0 < t := by
          rw [Set.uIcc_of_le hρr'] at ht
          rw [Set.mem_Icc] at ht
          exact lt_of_lt_of_le hρ0 ht.1
        have htne : t ≠ 0 := ne_of_gt htpos
        have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / t ^ 2) t :=
          (hasDerivAt_id t).inv (by simpa using htne)
        have hsq : HasDerivAt (fun x : ℝ => (x⁻¹) ^ 2)
            (2 * t⁻¹ * (-1 / t ^ 2)) t := by
          have h := hinv.mul hinv
          have hv : (-1 / t ^ 2) * (fun x : ℝ => x⁻¹) t +
              (fun x : ℝ => x⁻¹) t * (-1 / t ^ 2)
              = 2 * t⁻¹ * (-1 / t ^ 2) := by
            simp only []
            ring
          rw [hv] at h
          exact h.congr_of_eventuallyEq (by
            filter_upwards with y
            exact (pow_two _))
        have h1 : HasDerivAt (fun x : ℝ => -Real.pi * (x⁻¹) ^ 2)
            (-Real.pi * (2 * t⁻¹ * (-1 / t ^ 2))) t :=
          hsq.const_mul (-Real.pi)
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
          simpa using hasDerivAt_pow 2 t
        have h3 : HasDerivAt (fun x : ℝ => Real.pi * ‖c‖ ^ 2 * x ^ 2)
            (Real.pi * ‖c‖ ^ 2 * (2 * t)) t :=
          h2.const_mul (Real.pi * ‖c‖ ^ 2)
        have hΦraw : HasDerivAt
            (fun t : ℝ => -Real.pi * (t⁻¹) ^ 2 + Real.pi * ‖c‖ ^ 2 * t ^ 2)
            (-Real.pi * (2 * t⁻¹ * (-1 / t ^ 2)) +
              Real.pi * ‖c‖ ^ 2 * (2 * t)) t :=
          h1.add h3
        have hval : -Real.pi * (2 * t⁻¹ * (-1 / t ^ 2)) +
            Real.pi * ‖c‖ ^ 2 * (2 * t)
            = t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)) := by
          field_simp
        rw [hval] at hΦraw
        exact hΦraw
      have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ hInt
      rw [heq]
      have hrne : r ≠ 0 := ne_of_gt (lt_trans hρ0 hρr)
      have hρne : ρ ≠ 0 := ne_of_gt hρ0
      field_simp
      ring
    have hIntR : Integrable
        (fun t : ℝ => t * (2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2)))
        (volume.restrict (Set.Ioo ρ r)) :=
      IntegrableOn.congr_set_ae
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hρr').mp hInt)
        Ioo_ae_eq_Ioc
    rw [← ofReal_integral_eq_lintegral_ofReal hIntR hnn, hB]
  rw [hvol, hpolar, ← hradial]
  exact hmono

/-- Reduction of the Koebe quarter theorem to Bieberbach's second-coefficient bound. -/
theorem koebe_of_bieberbach
    (hB : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) →
      Set.InjOn g (Metric.ball (0 : ℂ) 1) → g 0 = 0 → deriv g 0 = 1 →
      ‖iteratedDeriv 2 g 0‖ ≤ 4)
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (h0 : f 0 = 0)
    (hderiv : deriv f 0 = 1) :
    Metric.ball (0 : ℂ) (1 / 4 : ℝ) ⊆ f '' Metric.ball (0 : ℂ) 1 := by
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  intro w hw
  have hwball : ‖w‖ < 1 / 4 := by
    have h := Metric.mem_ball.mp hw
    rwa [dist_zero_right] at h
  by_contra hcon
  have hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ w := by
    intro z hz hzw
    exact hcon ⟨z, hz, hzw⟩
  have hw0 : w ≠ 0 := by
    intro hww
    apply hcon
    refine ⟨0, hmem0, ?_⟩
    rw [h0]
    exact hww.symm
  have hfat : ∀ z ∈ Metric.ball (0 : ℂ) 1, HasDerivAt f (deriv f z) z :=
    fun z hz => hf.hasDerivAt (hopen.mem_nhds hz)
  have h1 : HasDerivAt f 1 0 := by
    have h := hfat 0 hmem0
    rwa [hderiv] at h
  have hu0 : HasDerivAt (fun y => w * f y) w 0 := by
    have h := h1.const_mul w
    rwa [mul_one] at h
  have hv0 : HasDerivAt (fun y => w - f y) (-1) 0 := by
    have h := (hasDerivAt_const (0 : ℂ) w).sub h1
    rw [show (0 : ℂ) - 1 = -1 from zero_sub 1] at h
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hv00 : (fun y => w - f y) 0 ≠ 0 := by
    have he : (fun y => w - f y) (0 : ℂ) = w := by simp [h0]
    rw [he]
    exact hw0
  have hdiv := hu0.div hv0 hv00
  have hgderiv : deriv (fun z => w * f z / (w - f z)) 0 = 1 := by
    have hlam : HasDerivAt (fun z => w * f z / (w - f z))
        ((w * ((fun y => w - f y) 0) - (fun z => w * f z) 0 * -1) /
          ((fun y => w - f y) 0) ^ 2) 0 :=
      hdiv.congr_of_eventuallyEq (by filter_upwards with y; rfl)
    have e := hlam.deriv
    rw [show ((fun y => w - f y) (0 : ℂ)) = w from by simp [h0],
      show ((fun z => w * f z) (0 : ℂ)) = 0 from by simp [h0]] at e
    rw [zero_mul, sub_zero, pow_two, div_self (mul_ne_zero hw0 hw0)] at e
    exact e
  have hu_at : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun y => w * f y) (w * deriv f z) z :=
    fun z hz => HasDerivAt.const_mul w (hfat z hz)
  have hv_at : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun y => w - f y) (-deriv f z) z := by
    intro z hz
    have h := (hasDerivAt_const z w).sub (hfat z hz)
    rw [show (0 : ℂ) - deriv f z = -deriv f z from zero_sub _] at h
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hvv : ∀ z ∈ Metric.ball (0 : ℂ) 1, (fun y => w - f y) z ≠ 0 := by
    intro z hz
    have he : (fun y => w - f y) z = w - f z := rfl
    rw [he]
    exact sub_ne_zero.mpr (fun h => hne z hz h.symm)
  have hg_at : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun z => w * f z / (w - f z))
        ((w * deriv f z * ((fun y => w - f y) z) -
          (fun z => w * f z) z * (-deriv f z)) /
          ((fun y => w - f y) z) ^ 2) z := by
    intro z hz
    exact ((hu_at z hz).div (hv_at z hz)
      (hvv z hz)).congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hderiv_eq : deriv (fun z => w * f z / (w - f z)) =ᶠ[nhds (0 : ℂ)]
      (fun z => (w * deriv f z * (w - f z) - w * f z * (-deriv f z)) /
        ((w - f z) * (w - f z))) := by
    filter_upwards [hnhds] with z hz
    have e := (hg_at z hz).deriv
    rw [pow_two] at e
    exact e
  have hdf : DifferentiableOn ℂ (deriv f) (Metric.ball (0 : ℂ) 1) :=
    hf.deriv hopen
  have hdd : HasDerivAt (deriv f) (deriv (deriv f) 0) 0 :=
    hdf.hasDerivAt (hopen.mem_nhds hmem0)
  have i2f_eq : iteratedDeriv 2 f 0 = deriv (deriv f) 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hA : HasDerivAt (fun z => w * deriv f z) (w * deriv (deriv f) 0) 0 :=
    HasDerivAt.const_mul w hdd
  have hE : HasDerivAt (fun z => -deriv f z) (-deriv (deriv f) 0) 0 := by
    have h := hdd.neg
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hC : HasDerivAt (fun z => w * f z) (w * 1) 0 := h1.const_mul w
  have hN : HasDerivAt
      (fun z => w * deriv f z * (w - f z) - w * f z * (-deriv f z))
      (((w * deriv (deriv f) 0) * (fun y => w - f y) 0 +
        (fun z => w * deriv f z) 0 * -1) -
        ((w * 1) * (fun z => -deriv f z) 0 +
          (fun z => w * f z) 0 * (-deriv (deriv f) 0))) 0 := by
    have hAV := hA.mul hv0
    have hCE := hC.mul hE
    have h := hAV.sub hCE
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hDraw : HasDerivAt (fun z => (w - f z) * (w - f z))
      ((-1) * (fun y => w - f y) 0 + (fun y => w - f y) 0 * (-1)) 0 := by
    have h := hv0.mul hv0
    exact h.congr_of_eventuallyEq (by filter_upwards with y; rfl)
  have hD0 : (fun z => (w - f z) * (w - f z)) 0 ≠ 0 := by
    have he : (fun z => (w - f z) * (w - f z)) (0 : ℂ) = w * w := by
      simp [h0]
    rw [he]
    exact mul_ne_zero hw0 hw0
  have hi2 : iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 =
      iteratedDeriv 2 f 0 + 2 / w := by
    have e1 : iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 =
        deriv (deriv (fun z => w * f z / (w - f z))) 0 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have e2 : deriv (deriv (fun z => w * f z / (w - f z))) 0 =
        deriv (fun z => (w * deriv f z * (w - f z) - w * f z * (-deriv f z)) /
          ((w - f z) * (w - f z))) 0 :=
      Filter.EventuallyEq.deriv_eq hderiv_eq
    have hQ := hN.div hDraw hD0
    have e4 : deriv (fun z => (w * deriv f z * (w - f z) -
        w * f z * (-deriv f z)) / ((w - f z) * (w - f z))) 0 =
        deriv ((fun z => w * deriv f z * (w - f z) - w * f z * (-deriv f z)) /
          (fun z => (w - f z) * (w - f z))) 0 := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards with y
      rfl
    have e5 := hQ.deriv
    rw [← e4] at e5
    simp only [] at e5
    rw [h0, hderiv, ← i2f_eq] at e5
    rw [e1, e2, e5]
    field_simp
    ring
  have hg_diffble : DifferentiableOn ℂ (fun z => w * f z / (w - f z))
      (Metric.ball (0 : ℂ) 1) :=
    ((differentiableOn_const w).mul hf).div
      ((differentiableOn_const w).sub hf)
      (fun z hz => sub_ne_zero.mpr (fun h => hne z hz h.symm))
  have ginj : Set.InjOn (fun z => w * f z / (w - f z))
      (Metric.ball (0 : ℂ) 1) := by
    intro z1 hz1 z2 hz2 heq
    have ha : w - f z1 ≠ 0 :=
      sub_ne_zero.mpr (fun h => hne z1 hz1 h.symm)
    have hb : w - f z2 ≠ 0 :=
      sub_ne_zero.mpr (fun h => hne z2 hz2 h.symm)
    simp only [] at heq
    rw [div_eq_div_iff ha hb] at heq
    have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
    have hab : f z1 = f z2 := by
      have h2 : w ^ 2 * (f z1 - f z2) = 0 := by linear_combination heq
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hw2
      · exact sub_eq_zero.mp h
    exact hinj hz1 hz2 hab
  have hg0 : (fun z => w * f z / (w - f z)) 0 = 0 := by simp [h0]
  have hBf : ‖iteratedDeriv 2 f 0‖ ≤ 4 := hB f hf hinj h0 hderiv
  have hgB : ‖iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0‖ ≤ 4 :=
    hB _ hg_diffble ginj hg0 hgderiv
  have h2w : ‖(2 : ℂ) / w‖ ≤ 8 := by
    have e : (2 : ℂ) / w =
        iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 -
          iteratedDeriv 2 f 0 := by
      rw [hi2]
      ring
    rw [e]
    calc ‖iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0 -
          iteratedDeriv 2 f 0‖
        ≤ ‖iteratedDeriv 2 (fun z => w * f z / (w - f z)) 0‖ +
          ‖iteratedDeriv 2 f 0‖ := norm_sub_le _ _
      _ ≤ 4 + 4 := by gcongr
      _ = 8 := by norm_num
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have h2wn : ‖(2 : ℂ) / w‖ = 2 / ‖w‖ := by
    rw [norm_div]
    norm_num
  rw [h2wn] at h2w
  have hge : 1 / 4 ≤ ‖w‖ := by
    rw [div_le_iff₀ hwpos] at h2w
    linarith
  linarith

theorem koebe_H_holo
    (s : ℂ → ℂ)
    (hs : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) 1)) :
    DifferentiableOn ℂ (fun z : ℂ => z * s (z ^ 2)) (Metric.ball (0 : ℂ) 1) := by
  have hsq : DifferentiableOn ℂ (fun z : ℂ => z ^ 2) (Metric.ball (0 : ℂ) 1) :=
    DifferentiableOn.pow differentiableOn_id 2
  have hmaps : Set.MapsTo (fun z : ℂ => z ^ 2) (Metric.ball (0 : ℂ) 1)
      (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have h1 : ‖z‖ < 1 := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    have hnn : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - 1)]
  exact differentiableOn_id.mul (hs.comp hsq hmaps)

theorem koebe_H_zero_iff
    (s : ℂ → ℂ)
    (hsne : ∀ w ∈ Metric.ball (0 : ℂ) 1, s w ≠ 0)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (z * s (z ^ 2) = 0) ↔ z = 0 := by
  have hsq_mem : z ^ 2 ∈ Metric.ball (0 : ℂ) 1 := by
    have h1 : ‖z‖ < 1 := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    have hnn : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - 1)]
  constructor
  · intro hcon
    rcases mul_eq_zero.mp hcon with h | h
    · exact h
    · exact absurd h (hsne _ hsq_mem)
  · intro h
    rw [h, zero_mul]

end Complex.KoebeQuarterWanted
end
