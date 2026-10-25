/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Def.Analysis.Complex.HartogsExtension.Part7


namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

theorem hartogsext_fderiv_uncurry_slice_diag
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x v : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    fderiv ℝ (Function.uncurry (hartogsextSlice i g))
        (x, WithLp.ofLp x i - t) (hartogsextDiagCLM i v) =
      fderiv ℝ g (x - EuclideanSpace.single i t) v := by
  let P : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
  have hcoord : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) P x := by
    change HasFDerivAt P P x
    exact P.hasFDerivAt
  have hpair : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦ (y, WithLp.ofLp y i - t))
      (hartogsextDiagCLM i) x := by
    change HasFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦
      (y, WithLp.ofLp y i - t))
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))).prod P) x
    have hpair' := (hasFDerivAt_id x).prodMk (hcoord.sub_const t)
    apply hpair'.congr_of_eventuallyEq
    filter_upwards with y
    rfl
  have hsliceDiff := (hartogsext_contDiff_uncurry_slice hg i).differentiable (by norm_num)
  have hleft := (hsliceDiff (x, WithLp.ofLp x i - t)).hasFDerivAt.comp x hpair
  have hright : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦
        g (y - EuclideanSpace.single i t))
      (fderiv ℝ g (x - EuclideanSpace.single i t)) x := by
    have hright' := (hg.differentiable (by norm_num)
      (x - EuclideanSpace.single i t)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const (EuclideanSpace.single i t))
    apply hright'.congr_of_eventuallyEq
    filter_upwards with y
    rfl
  have hleft' : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦
        g (y - EuclideanSpace.single i t))
      ((fderiv ℝ (Function.uncurry (hartogsextSlice i g))
        (x, WithLp.ofLp x i - t)).comp (hartogsextDiagCLM i)) x := by
    apply hleft.congr_of_eventuallyEq
    filter_upwards with y
    exact congrArg g (hartogsextReplace_sub i y t).symm
  have hmaps := hleft'.unique hright
  exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hmaps

theorem hartogsext_fderiv_partialCauchyGreen_apply
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (hartogsextPartialCauchyGreen i g) x v =
      ∫ t : ℂ, hartogsextCauchyGreenKernel t *
        fderiv ℝ g (x - EuclideanSpace.single i t) v := by
  obtain ⟨R, hRpos, hsupport⟩ := hartogsext_slice_uniform_support hgc i
  let k : Set ℂ := Metric.closedBall 0 R
  have hk : IsCompact k := isCompact_closedBall (0 : ℂ) R
  have hparam := hartogsext_contDiff_uncurry_slice hg i
  have hq := hasFDerivAt_convolution_right_with_param
    (ContinuousLinearMap.mul ℝ ℂ) isOpen_univ hk
    (fun p z hp hz ↦ hsupport p z hz)
    hartogsext_cauchyGreenKernel_locallyIntegrable hparam.contDiffOn
    (x, WithLp.ofLp x i) (Set.mem_univ x)
  let P : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
  have hcoord : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦ WithLp.ofLp y i) P x := by
    change HasFDerivAt P P x
    exact P.hasFDerivAt
  have hdiag : HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) ↦ (y, WithLp.ofLp y i))
      (hartogsextDiagCLM i) x := by
    change HasFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦
      (y, WithLp.ofLp y i))
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))).prod P) x
    have hdiag' := (hasFDerivAt_id x).prodMk hcoord
    apply hdiag'.congr_of_eventuallyEq
    filter_upwards with y
    rfl
  have hcomp := hq.comp x hdiag
  have hcomp' : HasFDerivAt (hartogsextPartialCauchyGreen i g)
      (((hartogsextCauchyGreenKernel ⋆[
        (ContinuousLinearMap.mul ℝ ℂ).precompR
          (EuclideanSpace ℂ (Fin n) × ℂ), volume]
          fun t : ℂ ↦ fderiv ℝ (Function.uncurry (hartogsextSlice i g)) (x, t))
        (WithLp.ofLp x i)).comp (hartogsextDiagCLM i)) x := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards with y
    rfl
  rw [hcomp'.fderiv, ContinuousLinearMap.comp_apply]
  have hDcont : Continuous
      (fun t : ℂ ↦ fderiv ℝ (Function.uncurry (hartogsextSlice i g)) (x, t)) :=
    (hparam.continuous_fderiv (by norm_num)).comp
      (continuous_const.prodMk continuous_id)
  have hDcompact : HasCompactSupport
      (fun t : ℂ ↦ fderiv ℝ (Function.uncurry (hartogsextSlice i g)) (x, t)) := by
    apply HasCompactSupport.of_support_subset_isCompact hk
    intro t ht
    by_contra htk
    have hevent : Filter.EventuallyEq (nhds (x, t))
        (Function.uncurry (hartogsextSlice i g)) (fun _ ↦ 0) := by
      filter_upwards [((isOpen_univ.prod hk.isClosed.isOpen_compl).mem_nhds
        ⟨Set.mem_univ x, htk⟩)] with q hqmem
      exact hsupport q.1 q.2 hqmem.2
    have hzero : fderiv ℝ (Function.uncurry (hartogsextSlice i g)) (x, t) = 0 :=
      (hasFDerivAt_zero_of_eventually_const (0 : ℂ) hevent).fderiv
    exact ht hzero
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable hDcompact hDcont
    (WithLp.ofLp x i) (hartogsextDiagCLM i v)]
  simp only [convolution_def]
  apply integral_congr_ae
  filter_upwards with t
  rw [hartogsext_fderiv_uncurry_slice_diag hg i x v t]
  exact ContinuousLinearMap.mul_apply' ℝ ℂ _ _

theorem hartogsext_continuous_replace_right
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
    Continuous (hartogsextReplace i x) := by
  unfold hartogsextReplace
  rw [show (fun z : ℂ ↦ x + EuclideanSpace.single i (z - WithLp.ofLp x i)) =
      fun z ↦ x + (z - WithLp.ofLp x i) • EuclideanSpace.single i 1 by
    funext z
    rw [hartogsext_single_eq_smul]]
  fun_prop

theorem hartogsext_integrable_kernel_fderiv
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x v : EuclideanSpace ℂ (Fin n)) :
    Integrable (fun t : ℂ ↦ hartogsextCauchyGreenKernel t *
      fderiv ℝ g (x - EuclideanSpace.single i t) v) := by
  let a : EuclideanSpace ℂ (Fin n) → ℂ := fun y ↦ fderiv ℝ g y v
  have hac : HasCompactSupport a := hgc.fderiv_apply ℝ v
  have ha : Continuous a :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨R, hRpos, hsupp⟩ := hartogsext_slice_uniform_support hac i
  have hsliceCompact : HasCompactSupport (hartogsextSlice i a x) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℂ) R)
    intro z hz
    by_contra hzb
    exact hz (hsupp x z hzb)
  have hsliceContinuous : Continuous (hartogsextSlice i a x) :=
    ha.comp (hartogsext_continuous_replace_right i x)
  have hexists := hsliceCompact.convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable hsliceContinuous
    (WithLp.ofLp x i)
  apply hexists.congr
  filter_upwards with t
  rw [ContinuousLinearMap.mul_apply']
  change hartogsextCauchyGreenKernel t *
      fderiv ℝ g (hartogsextReplace i x (WithLp.ofLp x i - t)) v =
    hartogsextCauchyGreenKernel t *
      fderiv ℝ g (x - EuclideanSpace.single i t) v
  rw [hartogsextReplace_sub]

theorem hartogsext_barPartial_partialCauchyGreen
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i j : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextBarPartial j (hartogsextPartialCauchyGreen i g) x =
      hartogsextPartialCauchyGreen i (hartogsextBarPartial j g) x := by
  rw [hartogsextBarPartial]
  rw [hartogsext_fderiv_partialCauchyGreen_apply hgc hg i x
    (EuclideanSpace.single j 1)]
  rw [hartogsext_fderiv_partialCauchyGreen_apply hgc hg i x
    (EuclideanSpace.single j Complex.I)]
  unfold hartogsextPartialCauchyGreen hartogsextCauchyGreenTransform
  simp only [convolution_def]
  have h1 := hartogsext_integrable_kernel_fderiv hgc hg i x
    (EuclideanSpace.single j 1)
  have hI := hartogsext_integrable_kernel_fderiv hgc hg i x
    (EuclideanSpace.single j Complex.I)
  rw [← integral_const_mul]
  rw [← integral_add h1 (hI.const_mul Complex.I), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [ContinuousLinearMap.mul_apply']
  change _ = hartogsextCauchyGreenKernel t *
    hartogsextBarPartial j g
      (hartogsextReplace i x (WithLp.ofLp x i - t))
  rw [hartogsextReplace_sub]
  simp only [hartogsextBarPartial]
  ring

/-- A complex-differentiable function has vanishing Wirtinger derivative. -/
theorem barDeriv_eq_zero_of_differentiableAt
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) : barDeriv f z = 0 := by
  rw [barDeriv, hf.fderiv_restrictScalars (𝕜 := ℝ)]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [show Complex.I = Complex.I • (1 : ℂ) by simp, map_smul]
  simp only [smul_eq_mul]
  rw [mul_one, ← mul_assoc, Complex.I_mul_I]
  simp

/-- A real-differentiable function with vanishing Wirtinger derivative is complex
differentiable. -/
theorem differentiableAt_of_barDeriv_eq_zero
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hbar : barDeriv f z = 0) : DifferentiableAt ℂ f z := by
  let L : ℂ →L[ℝ] ℂ := fderiv ℝ f z
  have hsum : L 1 + Complex.I * L Complex.I = 0 := by
    have htwo : (2 : ℂ)⁻¹ ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hbar).resolve_left htwo
  have hIL : L Complex.I = Complex.I * L 1 := by
    have hneg : Complex.I * L Complex.I = -L 1 :=
      eq_neg_of_add_eq_zero_right hsum
    calc
      L Complex.I = (-(Complex.I * Complex.I)) * L Complex.I := by
        rw [Complex.I_mul_I]
        simp
      _ = -Complex.I * (Complex.I * L Complex.I) := by ring
      _ = -Complex.I * (-L 1) := by rw [hneg]
      _ = Complex.I * L 1 := by ring
  let A : ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ (L 1)
  apply (differentiableAt_iff_restrictScalars ℝ hf).2
  refine ⟨A, ?_⟩
  ext x
  have hx : x = x.re • (1 : ℂ) + x.im • Complex.I := by
    simp only [RCLike.real_smul_eq_coe_mul, mul_one]
    exact Complex.re_add_im x |>.symm
  have hLx : L x = x * L 1 := by
    rw [hx, map_add, map_smul, map_smul, hIL]
    simp only [RCLike.real_smul_eq_coe_mul, mul_one]
    rw [← mul_assoc, ← add_mul]
  rw [hLx]
  change L 1 * x = x * L 1
  exact mul_comm _ _

theorem hartogsext_differentiableAt_of_barPartial_eq_zero
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hbar : ∀ i, hartogsextBarPartial i f x = 0) : DifferentiableAt ℂ f x := by
  let L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ := fderiv ℝ f x
  have hLI (i : Fin n) : L (EuclideanSpace.single i Complex.I) =
      Complex.I * L (EuclideanSpace.single i 1) := by
    have hsum : L (EuclideanSpace.single i 1) +
        Complex.I * L (EuclideanSpace.single i Complex.I) = 0 := by
      have htwo : (2 : ℂ)⁻¹ ≠ 0 := by norm_num
      exact (mul_eq_zero.mp (hbar i)).resolve_left htwo
    have hneg : Complex.I * L (EuclideanSpace.single i Complex.I) =
        -L (EuclideanSpace.single i 1) := eq_neg_of_add_eq_zero_right hsum
    calc
      L (EuclideanSpace.single i Complex.I) =
          (-(Complex.I * Complex.I)) * L (EuclideanSpace.single i Complex.I) := by
        rw [Complex.I_mul_I]
        simp
      _ = -Complex.I *
          (Complex.I * L (EuclideanSpace.single i Complex.I)) := by ring
      _ = -Complex.I * (-L (EuclideanSpace.single i 1)) := by rw [hneg]
      _ = Complex.I * L (EuclideanSpace.single i 1) := by ring
  have hLsingle (i : Fin n) (z : ℂ) :
      L (z • EuclideanSpace.single i 1) =
        z * L (EuclideanSpace.single i 1) := by
    have hz : z • EuclideanSpace.single i 1 =
        z.re • EuclideanSpace.single i 1 +
          z.im • EuclideanSpace.single i Complex.I := by
      ext j
      by_cases hji : j = i
      · subst j
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_eq_same,
          RCLike.real_smul_eq_coe_mul, smul_eq_mul, mul_one]
        exact Complex.re_add_im z |>.symm
      · simp [hji]
    rw [hz, map_add, map_smul, map_smul, hLI]
    simp only [RCLike.real_smul_eq_coe_mul]
    rw [← mul_assoc, ← add_mul]
    exact congrArg (fun w : ℂ ↦ w * L (EuclideanSpace.single i 1))
      (Complex.re_add_im z)
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
    ∑ i : Fin n, ((ContinuousLinearMap.mul ℂ ℂ).flip
      (L (EuclideanSpace.single i 1))).comp (EuclideanSpace.proj (𝕜 := ℂ) i)
  apply (differentiableAt_iff_restrictScalars ℝ hf).2
  refine ⟨A, ?_⟩
  ext y
  have hy : y = ∑ i : Fin n,
      WithLp.ofLp y i • EuclideanSpace.single i 1 := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr y).symm
  calc
    A.restrictScalars ℝ y = ∑ i : Fin n,
        WithLp.ofLp y i * L (EuclideanSpace.single i 1) := by
      simp only [A, ContinuousLinearMap.coe_restrictScalars',
        sum_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply',
        EuclideanSpace.coe_proj]
    _ = ∑ i : Fin n, L (WithLp.ofLp y i • EuclideanSpace.single i 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hLsingle i (WithLp.ofLp y i)).symm
    _ = L y := by rw [← map_sum, ← hy]

theorem hartogsext_cauchyGreenTransform_hasFDerivAt
    {g : ℂ → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (z : ℂ) :
    HasFDerivAt (hartogsextCauchyGreenTransform g)
      ((hartogsextCauchyGreenKernel ⋆[
        (ContinuousLinearMap.mul ℝ ℂ).precompR ℂ, volume] fderiv ℝ g) z) z := by
  exact hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable hg z

theorem hartogsext_barDeriv_cauchyGreenTransform
    {g : ℂ → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (z : ℂ) :
    barDeriv (hartogsextCauchyGreenTransform g) z =
      (hartogsextCauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] barDeriv g) z := by
  have hD := hartogsext_cauchyGreenTransform_hasFDerivAt hgc hg z
  have hDf : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hconv_one := (hgc.fderiv_apply ℝ (1 : ℂ)).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℂ) hartogsext_cauchyGreenKernel_locallyIntegrable
    ((continuous_clm_apply.mp hDf) 1)
  have hconv_I := (hgc.fderiv_apply ℝ Complex.I).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℂ) hartogsext_cauchyGreenKernel_locallyIntegrable
    ((continuous_clm_apply.mp hDf) Complex.I)
  rw [barDeriv, hD.fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable (hgc.fderiv ℝ) hDf z 1]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    hartogsext_cauchyGreenKernel_locallyIntegrable (hgc.fderiv ℝ) hDf z Complex.I]
  simp only [convolution_def]
  change (2 : ℂ)⁻¹ *
      ((∫ t, hartogsextCauchyGreenKernel t * fderiv ℝ g (z - t) 1) +
        Complex.I * ∫ t, hartogsextCauchyGreenKernel t * fderiv ℝ g (z - t) Complex.I) =
    ∫ t, hartogsextCauchyGreenKernel t * barDeriv g (z - t)
  have hone : Integrable
      (fun t ↦ hartogsextCauchyGreenKernel t * fderiv ℝ g (z - t) 1) volume :=
    hconv_one z
  have hI : Integrable
      (fun t ↦ hartogsextCauchyGreenKernel t * fderiv ℝ g (z - t) Complex.I) volume :=
    hconv_I z
  rw [← integral_const_mul]
  rw [← integral_add hone (hI.const_mul Complex.I), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [barDeriv]
  ring

end Complex.HartogsWanted
