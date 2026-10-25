/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.LeftRightNhds
import Def.Analysis.Complex.LoomanMenchoff.Part3
/-!
# The Looman–Menchoff theorem

This file proves that a continuous complex-valued function with everywhere-existing partial
derivatives satisfying the Cauchy–Riemann equations is complex differentiable.
-/


namespace MetaMathlibExt

open Set Filter MeasureTheory Metric Finset

open BoxIntegral

open scoped ENNReal Interval NNReal Topology BoxIntegral Matrix

noncomputable section

theorem looman_boxAdditive_eq_zero
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Box ι} {F : Set (ι → ℝ)} (hF : IsClosed F)
    (g : ι →ᵇᵃ[I] E) {C : ℝ} (hC : 0 ≤ C)
    (r₀ : (ι → ℝ) → Ioi (0 : ℝ))
    (hzero : ∀ x ∈ Box.Icc I, x ∉ F → ∀ J ≤ I,
      Box.Icc J ⊆ closedBall x (r₀ x) → g J = 0)
    (hbound : ∀ J ≤ I, J.distortion ≤ I.distortion → ∀ x ∈ Box.Icc J, x ∈ F →
      ‖g J‖ ≤ C * volume.real ((J : Set (ι → ℝ)) \ F)) :
    g I = 0 := by
  classical
  let q : (ι → ℝ) → ℝ := Fᶜ.indicator (fun _ ↦ 1)
  have hqLeb : IntegrableOn q (I : Set (ι → ℝ)) volume := by
    apply IntegrableOn.indicator
      (integrableOn_const (I.measure_coe_lt_top volume).ne) hF.measurableSet.compl
  have hqBox : BoxIntegral.Integrable I IntegrationParams.GP q
      volume.toBoxAdditive.toSMul :=
    (hqLeb.hasBoxIntegral IntegrationParams.GP rfl).integrable
  have hqIntegral (J : Box ι) (hJI : J ≤ I) :
      BoxIntegral.integral J IntegrationParams.GP q volume.toBoxAdditive.toSMul =
        volume.real ((J : Set (ι → ℝ)) \ F) := by
    rw [(hqLeb.mono_set (Box.coe_subset_coe.2 hJI)).hasBoxIntegral
      IntegrationParams.GP rfl |>.integral_eq]
    simp only [q]
    rw [setIntegral_indicator hF.measurableSet.compl, setIntegral_one_eq_measureReal]
    congr 1
  apply norm_eq_zero.mp
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    let ε' := ε / (C + 1)
    have hC1 : 0 < C + 1 := by linarith
    have hε' : 0 < ε' := div_pos hε hC1
    let c : ℝ≥0 := I.distortion
    let r : (ι → ℝ) → Ioi (0 : ℝ) := fun x ↦
      min (hqBox.convergenceR ε' c x) (r₀ x)
    obtain ⟨π, hπ, hπpart⟩ := IntegrationParams.GP.exists_memBaseSet_isPartition
      I (by exact le_rfl) r
    have hπq : IntegrationParams.GP.MemBaseSet I c
        (hqBox.convergenceR ε' c) π :=
      hπ.mono I le_rfl le_rfl fun _ _ ↦ min_le_left _ _
    let πF := π.filter fun J ↦ π.tag J ∈ F
    have hπFq : IntegrationParams.GP.MemBaseSet I c
        (hqBox.convergenceR ε' c) πF := hπq.filter _
    have hsacks := hqBox.dist_integralSum_sum_integral_le_of_memBaseSet hε' hπFq
    have hsumVol :
        (∑ J ∈ πF.boxes, volume.real ((J : Set (ι → ℝ)) \ F)) ≤ ε' := by
      have hsum0 : BoxIntegral.integralSum q volume.toBoxAdditive.toSMul πF = 0 := by
        rw [BoxIntegral.integralSum]
        apply sum_eq_zero
        intro J hJ
        have hJ' : J ∈ π.filter (fun J ↦ π.tag J ∈ F) := by
          simpa [πF] using hJ
        have hJF : π.tag J ∈ F := (π.mem_filter.1 hJ').2
        have hq0 : q (πF.tag J) = 0 := by
          change q (π.tag J) = 0
          simp [q, hJF]
        simp [hq0]
      rw [hsum0] at hsacks
      have hint : (∑ J ∈ πF.boxes,
          BoxIntegral.integral J IntegrationParams.GP q volume.toBoxAdditive.toSMul) =
          ∑ J ∈ πF.boxes, volume.real ((J : Set (ι → ℝ)) \ F) := by
        apply sum_congr rfl
        intro J hJ
        exact hqIntegral J (πF.le_of_mem hJ)
      rw [hint] at hsacks
      rw [dist_zero_left, Real.norm_eq_abs] at hsacks
      exact (le_abs_self _).trans hsacks
    have hnotF (J : Box ι) (hJ : J ∈ π.boxes) (ht : π.tag J ∉ F) : g J = 0 := by
      apply hzero (π.tag J) (π.tag_mem_Icc J) ht J (π.le_of_mem hJ)
      exact (hπ.1 J hJ).trans fun y hy ↦ closedBall_subset_closedBall
        (min_le_right _ _) hy
    have hgI : g I = ∑ J ∈ πF.boxes, g J := by
      have : (∑ J ∈ π.boxes with π.tag J ∉ F, g J) = 0 := by
        apply sum_eq_zero
        intro J hJ
        exact hnotF J (Finset.mem_filter.1 hJ).1 (Finset.mem_filter.1 hJ).2
      calc
        g I = ∑ J ∈ π.boxes, g J := (g.sum_partition_boxes le_rfl hπpart).symm
        _ = (∑ J ∈ π.boxes with π.tag J ∈ F, g J) +
            ∑ J ∈ π.boxes with π.tag J ∉ F, g J :=
          (sum_filter_add_sum_filter_not π.boxes (fun J ↦ π.tag J ∈ F) g).symm
        _ = ∑ J ∈ πF.boxes, g J := by
          rw [this, add_zero]
          rfl
    rw [hgI]
    calc
      ‖∑ J ∈ πF.boxes, g J‖ ≤ ∑ J ∈ πF.boxes, ‖g J‖ := norm_sum_le _ _
      _ ≤ ∑ J ∈ πF.boxes, C * volume.real ((J : Set (ι → ℝ)) \ F) := by
        gcongr with J hJ
        have hJ' : J ∈ π.filter (fun J ↦ π.tag J ∈ F) := by
          simpa [πF] using hJ
        have hJπ : J ∈ π := (π.mem_filter.1 hJ').1
        apply hbound J (π.le_of_mem hJπ)
          ((π.distortion_le_of_mem hJπ).trans (hπ.3 (by change true = true; rfl)))
          (π.tag J)
        · exact hπ.2 (by change true = true; rfl) J hJπ
        · exact (π.mem_filter.1 hJ').2
      _ = C * ∑ J ∈ πF.boxes, volume.real ((J : Set (ι → ℝ)) \ F) := by
        rw [mul_sum]
      _ ≤ C * ε' := mul_le_mul_of_nonneg_left hsumVol hC
      _ ≤ ε := by
        calc
          C * ε' ≤ (C + 1) * ε' :=
            mul_le_mul_of_nonneg_right (by linarith) hε'.le
          _ = ε := by
            dsimp [ε']
            field_simp
      _ = 0 + ε := (zero_add ε).symm
  · exact norm_nonneg _

theorem looman_rectBoundary_swap_x (f : ℂ → ℂ) (A B C D : ℝ) :
    loomanRectBoundary f B A C D = -loomanRectBoundary f A B C D := by
  unfold loomanRectBoundary
  rw [intervalIntegral.integral_symm B A]
  have hv : (∫ y in C..D, f (loomanPoint A y) - f (loomanPoint B y)) =
      -∫ y in C..D, f (loomanPoint B y) - f (loomanPoint A y) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext y
    ring
  rw [hv]
  ring

theorem looman_rectBoundary_swap_y (f : ℂ → ℂ) (A B C D : ℝ) :
    loomanRectBoundary f A B D C = -loomanRectBoundary f A B C D := by
  unfold loomanRectBoundary
  rw [intervalIntegral.integral_symm D C]
  have hh : (∫ x in A..B, f (loomanPoint x D) - f (loomanPoint x C)) =
      -∫ x in A..B, f (loomanPoint x C) - f (loomanPoint x D) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  rw [hh]
  ring

theorem looman_differentiableOn_Ioo_of_rectBoundary_eq_zero
    {f : ℂ → ℂ} {A B C D : ℝ} (hcont : Continuous f)
    (hzero : ∀ a b c d, A < a → a < b → b < B →
      C < c → c < d → d < D → loomanRectBoundary f a b c d = 0) :
    DifferentiableOn ℂ f (Ioo A B ×ℂ Ioo C D) := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
    (isOpen_Ioo.reProdIm isOpen_Ioo)).1
  refine ⟨?_, hcont.continuousOn⟩
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  by_cases hzre : z.re = w.re
  · simp [hzre]
  by_cases hzim : z.im = w.im
  · simp [hzim]
  let a := min z.re w.re
  let b := max z.re w.re
  let c := min z.im w.im
  let d := max z.im w.im
  have hab : a < b := min_lt_max.2 hzre
  have hcd : c < d := min_lt_max.2 hzim
  have hmin : loomanPoint a c ∈ Complex.Rectangle z w := by
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    exact ⟨by simp [loomanPoint, a, Set.uIcc],
      by simp [loomanPoint, c, Set.uIcc]⟩
  have hmax : loomanPoint b d ∈ Complex.Rectangle z w := by
    rw [Complex.Rectangle, Complex.mem_reProdIm]
    exact ⟨by simp [loomanPoint, b, Set.uIcc],
      by simp [loomanPoint, d, Set.uIcc]⟩
  have hminU := hzw hmin
  have hmaxU := hzw hmax
  have hAa : A < a := by simpa [loomanPoint] using hminU.1.1
  have hbB : b < B := by simpa [loomanPoint] using hmaxU.1.2
  have hCc : C < c := by simpa [loomanPoint] using hminU.2.1
  have hdD : d < D := by simpa [loomanPoint] using hmaxU.2.2
  have h0 := hzero a b c d hAa hab hbB hCc hcd hdD
  have horiented : loomanRectBoundary f z.re w.re z.im w.im = 0 := by
    rcases le_total z.re w.re with hx | hx <;>
      rcases le_total z.im w.im with hy | hy
    · simpa [a, b, c, d, min_eq_left hx, max_eq_right hx,
        min_eq_left hy, max_eq_right hy] using h0
    · have h0' : loomanRectBoundary f z.re w.re w.im z.im = 0 := by
        simpa [a, b, c, d, min_eq_left hx, max_eq_right hx,
          min_eq_right hy, max_eq_left hy] using h0
      rw [looman_rectBoundary_swap_y]
      simpa using congrArg Neg.neg h0'
    · have h0' : loomanRectBoundary f w.re z.re z.im w.im = 0 := by
        simpa [a, b, c, d, min_eq_right hx, max_eq_left hx,
          min_eq_left hy, max_eq_right hy] using h0
      rw [looman_rectBoundary_swap_x]
      simpa using congrArg Neg.neg h0'
    · have h0' : loomanRectBoundary f w.re z.re w.im z.im = 0 := by
        simpa [a, b, c, d, min_eq_right hx, max_eq_left hx,
          min_eq_right hy, max_eq_left hy] using h0
      rw [looman_rectBoundary_swap_x, looman_rectBoundary_swap_y]
      simpa using h0'
  have hh₁ : IntervalIntegrable
      (fun x : ℝ ↦ f (loomanPoint x z.im)) volume z.re w.re :=
    (show Continuous (fun x : ℝ ↦ f (loomanPoint x z.im)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hh₂ : IntervalIntegrable
      (fun x : ℝ ↦ f (loomanPoint x w.im)) volume z.re w.re :=
    (show Continuous (fun x : ℝ ↦ f (loomanPoint x w.im)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hv₁ : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint w.re y)) volume z.im w.im :=
    (show Continuous (fun y : ℝ ↦ f (loomanPoint w.re y)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  have hv₂ : IntervalIntegrable
      (fun y : ℝ ↦ f (loomanPoint z.re y)) volume z.im w.im :=
    (show Continuous (fun y : ℝ ↦ f (loomanPoint z.re y)) by
      unfold loomanPoint
      fun_prop).intervalIntegrable _ _
  rw [loomanRectBoundary, intervalIntegral.integral_sub hh₁ hh₂,
    intervalIntegral.integral_sub hv₁ hv₂] at horiented
  simp only [loomanPoint] at horiented
  simp only [smul_eq_mul]
  linear_combination horiented

end
end MetaMathlibExt
