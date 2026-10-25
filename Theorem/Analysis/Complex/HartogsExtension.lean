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


namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

theorem hartogsext_fderiv_single_eq_deriv
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (i : Fin n) (hf : DifferentiableAt ℂ f x) :
    fderiv ℂ f x (EuclideanSpace.single i 1) =
      deriv (fun z : ℂ ↦ f (x + z • EuclideanSpace.single i 1)) 0 := by
  have hline : HasDerivAt (fun z : ℂ ↦ x + z • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) 0 := by
    simpa using
      ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).smul_const (EuclideanSpace.single i 1)).const_add x
  have hf₀ : DifferentiableAt ℂ f (x + (0 : ℂ) • EuclideanSpace.single i 1) := by
    simpa using hf
  change fderiv ℂ f x (EuclideanSpace.single i 1) =
    deriv (f ∘ fun z : ℂ ↦ x + z • EuclideanSpace.single i 1) 0
  simpa using (hf₀.hasFDerivAt.comp_hasDerivAt 0 hline).deriv.symm

theorem hartogsext_line_closedBall_subset
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {x₀ x : EuclideanSpace ℂ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.ball x₀ r) (hball : Metric.ball x₀ (4 * r) ⊆ s)
    (i : Fin n) :
    Metric.closedBall (0 : ℂ) (2 * r) ⊆
      (fun z : ℂ ↦ x + z • EuclideanSpace.single i 1) ⁻¹' s := by
  intro z hz
  apply hball
  rw [Metric.mem_ball]
  calc
    dist (x + z • EuclideanSpace.single i 1) x₀ ≤
        dist (x + z • EuclideanSpace.single i 1) x + dist x x₀ := dist_triangle _ _ _
    _ = ‖z‖ + dist x x₀ := by
      simp [dist_eq_norm, norm_smul]
    _ < 4 * r := by
      have hz' : ‖z‖ ≤ 2 * r := by simpa [Metric.mem_closedBall] using hz
      have hx' : dist x x₀ < r := Metric.mem_ball.1 hx
      linarith

theorem hartogsext_continuousOn_circle_partial
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} {x₀ : EuclideanSpace ℂ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball x₀ (4 * r) ⊆ s)
    (hf : ContinuousOn f s) (i : Fin n) :
    ContinuousOn
      (fun x ↦ ∮ z in C(0, 2 * r),
        (z ^ 2)⁻¹ * f (x + z • EuclideanSpace.single i 1))
      (Metric.ball x₀ r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let q : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball x₀ r
  let _ : LocallyCompactSpace q :=
    IsOpen.locallyCompactSpace (by simp [q])
  have hfcomp : Continuous (fun p : q × ℝ ↦
      f (p.1.1 + circleMap 0 (2 * r) p.2 • EuclideanSpace.single i 1)) := by
    apply hf.comp_continuous (by fun_prop)
    intro p
    apply hartogsext_line_closedBall_subset hr p.1.2 hball i
    exact Metric.sphere_subset_closedBall (circleMap_mem_sphere 0 (by positivity) p.2)
  have hcircle (p : q × ℝ) : circleMap 0 (2 * r) p.2 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_circleMap_zero, abs_of_pos (by positivity : 0 < 2 * r)]
    positivity
  have hcirclecont : Continuous (fun p : q × ℝ ↦ circleMap 0 (2 * r) p.2) := by
    fun_prop
  have hinv : Continuous (fun p : q × ℝ ↦ ((circleMap 0 (2 * r) p.2) ^ 2)⁻¹) :=
    (hcirclecont.pow 2).inv₀ fun p ↦ pow_ne_zero _ (hcircle p)
  have hint : Continuous (fun p : q × ℝ ↦
      deriv (circleMap 0 (2 * r)) p.2 *
        ((circleMap 0 (2 * r) p.2) ^ 2)⁻¹ *
          f (p.1.1 + circleMap 0 (2 * r) p.2 • EuclideanSpace.single i 1)) := by
    simp_rw [deriv_circleMap]
    exact ((hcirclecont.mul continuous_const).mul hinv).mul hfcomp
  have hc := continuous_parametric_integral_of_continuous
    (μ := MeasureTheory.volume) (s := Set.Icc (0 : ℝ) (2 * Real.pi))
    (f := fun x : q ↦ fun θ : ℝ ↦
      deriv (circleMap 0 (2 * r)) θ * ((circleMap 0 (2 * r) θ) ^ 2)⁻¹ *
        f (x.1 + circleMap 0 (2 * r) θ • EuclideanSpace.single i 1))
    hint isCompact_Icc
  apply hc.congr
  intro x
  rw [Set.domRestrict_apply, circleIntegral_def_Icc]
  simp only [smul_eq_mul, mul_assoc]

theorem hartogsext_fderiv_single_eq_circleIntegral
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} {x₀ x : EuclideanSpace ℂ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hs : IsOpen s)
    (hball : Metric.ball x₀ (4 * r) ⊆ s) (hf : DifferentiableOn ℂ f s)
    (hx : x ∈ Metric.ball x₀ r) (i : Fin n) :
    fderiv ℂ f x (EuclideanSpace.single i 1) =
      (2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C(0, 2 * r), (z ^ 2)⁻¹ * f (x + z • EuclideanSpace.single i 1) := by
  let line : ℂ → EuclideanSpace ℂ (Fin n) :=
    fun z ↦ x + z • EuclideanSpace.single i 1
  let v : Set ℂ := line ⁻¹' s
  have hv : IsOpen v := hs.preimage (by fun_prop)
  have hline : Differentiable ℂ line := by
    dsimp [line]
    fun_prop
  have hg : DifferentiableOn ℂ (fun z ↦ f (line z)) v := by
    intro z hz
    exact ((hf.differentiableAt (hs.mem_nhds hz)).comp z (hline z)).differentiableWithinAt
  have hclosed : Metric.closedBall (0 : ℂ) (2 * r) ⊆ v := by
    exact hartogsext_line_closedBall_subset hr hx hball i
  have hformula :=
    Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      hv hclosed hg (Metric.mem_ball_self (by positivity : 0 < 2 * r))
  have hxs : x ∈ s := by
    apply hball
    rw [Metric.mem_ball] at hx ⊢
    linarith
  calc
    fderiv ℂ f x (EuclideanSpace.single i 1) = deriv (fun z ↦ f (line z)) 0 := by
      exact hartogsext_fderiv_single_eq_deriv i
        (hf.differentiableAt (hs.mem_nhds hxs))
    _ = (2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C(0, 2 * r), (z ^ 2)⁻¹ * f (line z) := by
      simpa [sub_zero, smul_eq_mul] using hformula.symm
    _ = (2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C(0, 2 * r), (z ^ 2)⁻¹ * f (x + z • EuclideanSpace.single i 1) := by
      rfl

theorem hartogsext_continuousOn_fderiv_single
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) (i : Fin n) :
    ContinuousOn (fun x ↦ fderiv ℂ f x (EuclideanSpace.single i 1)) s := by
  rw [hs.continuousOn_iff]
  intro x hx
  rcases Metric.isOpen_iff.mp hs x hx with ⟨ε, hε, hεs⟩
  let r := ε / 4
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hball : Metric.ball x (4 * r) ⊆ s := by
    have hradius : (4 : ℝ) * (ε / 4) = ε := by ring
    simpa only [r, hradius] using hεs
  have hcircle := hartogsext_continuousOn_circle_partial
    hr hball hf.continuousOn i
  have hscaled : ContinuousOn
      (fun y ↦ (2 * Real.pi * Complex.I)⁻¹ *
        ∮ z in C(0, 2 * r), (z ^ 2)⁻¹ * f (y + z • EuclideanSpace.single i 1))
      (Metric.ball x r) :=
    continuousOn_const.mul hcircle
  have hderiv : ContinuousOn
      (fun y ↦ fderiv ℂ f y (EuclideanSpace.single i 1)) (Metric.ball x r) :=
    hscaled.congr fun y hy ↦
      hartogsext_fderiv_single_eq_circleIntegral hr hs hball hf hy i
  exact hderiv.continuousAt (Metric.ball_mem_nhds x hr)

/-- The derivative of a complex-differentiable scalar function on an open subset of `ℂⁿ` is
continuous. In particular, the function is `C¹` there. -/
theorem continuousOn_fderiv_of_differentiableOn
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) : ContinuousOn (fderiv ℂ f) s := by
  have hsingle (i : Fin n) :
      ContinuousOn (fun x ↦ fderiv ℂ f x (EuclideanSpace.single i 1)) s :=
    hartogsext_continuousOn_fderiv_single hs hf i
  have hfd : ContinuousOn (fderiv ℂ f) s := by
    rw [continuousOn_clm_apply]
    intro y
    have hsum : ContinuousOn
        (fun x ↦ ∑ i : Fin n,
          WithLp.ofLp y i * fderiv ℂ f x (EuclideanSpace.single i 1)) s := by
      apply continuousOn_finsetSum Finset.univ
      intro i hi
      exact continuousOn_const.mul (hsingle i)
    apply hsum.congr
    intro x hx
    change fderiv ℂ f x y = ∑ i : Fin n,
      WithLp.ofLp y i * fderiv ℂ f x (EuclideanSpace.single i 1)
    have hy : y = ∑ i : Fin n,
        WithLp.ofLp y i • EuclideanSpace.single i 1 := by
      simpa using ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr y).symm
    conv_lhs => rw [hy]
    simp
  exact hfd

theorem hartogsext_differentiableOn_contDiffOn_one_real
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) : ContDiffOn ℝ 1 f s := by
  have hcomplex := continuousOn_fderiv_of_differentiableOn hs hf
  have hrestricted : ContinuousOn
      (fun x ↦ (fderiv ℂ f x).restrictScalars ℝ) s :=
    (ContinuousLinearMap.restrictScalarsL ℂ
      (EuclideanSpace ℂ (Fin n)) ℂ ℝ ℝ).continuous.comp_continuousOn hcomplex
  have hreal : ContinuousOn (fderiv ℝ f) s := by
    apply hrestricted.congr
    intro x hx
    exact (hf.differentiableAt (hs.mem_nhds hx)).fderiv_restrictScalars (𝕜 := ℝ)
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hs).2
  exact ⟨hf.restrictScalars ℝ, by simp, contDiffOn_zero.mpr hreal⟩

theorem hartogsext_contDiff_mul_of_tsupport_subset
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f a : EuclideanSpace ℂ (Fin n) → ℂ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) (ha : ContDiff ℝ 1 a) (has : tsupport a ⊆ s) :
    ContDiff ℝ 1 (fun x ↦ f x * a x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact ((hf x hx).contDiffAt (hs.mem_nhds hx)).mul ha.contDiffAt
  · have hxt : x ∉ tsupport a := fun h ↦ hx (has h)
    have ha0 : Filter.EventuallyEq (nhds x) a (fun _ ↦ 0) := by
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hxt] with y hy
      rw [mem_compl_iff] at hy
      apply Classical.byContradiction
      intro hay
      exact hy (subset_tsupport a hay)
    have hzero : ContDiffAt ℝ 1
        (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : ℂ)) x := contDiffAt_const
    apply hzero.congr_of_eventuallyEq
    filter_upwards [ha0] with y hy
    simp [hy]

theorem hartogsext_exists_cutoff
    {n : ℕ} {U K : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : EuclideanSpace ℂ (Fin n) → ℝ,
      ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
        ∃ V, IsOpen V ∧ K ⊆ V ∧ Set.EqOn χ (fun _ ↦ 1) V := by
  obtain ⟨W, hWopen, hKW, hWcompact⟩ :=
    exists_isOpen_superset_and_isCompact_closure hK
  have hUWopen : IsOpen (U ∩ W) := hU.inter hWopen
  have hKUW : K ⊆ U ∩ W := fun x hx ↦ ⟨hKU hx, hKW hx⟩
  obtain ⟨S, hSopen, hKS, hSsub⟩ :=
    hK.exists_isOpen_closure_subset (hUWopen.mem_nhdsSet.mpr hKUW)
  have hScompact : IsCompact (closure S) :=
    hWcompact.of_isClosed_subset isClosed_closure
      ((hSsub.trans inter_subset_right).trans subset_closure)
  obtain ⟨V, hVopen, hKV, hVsub⟩ :=
    hK.exists_isOpen_closure_subset (hSopen.mem_nhdsSet.mpr hKS)
  obtain ⟨χ, hχdiff, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 2) hSopen isClosed_closure hVsub
  refine ⟨χ, hχdiff, ?_, ?_, V, hVopen, hKV, ?_⟩
  · rw [HasCompactSupport, tsupport, hχsupport]
    exact hScompact
  · rw [tsupport, hχsupport]
    exact hSsub.trans inter_subset_left
  · intro x hx
    exact (hχone x).mp (subset_closure hx)

end Complex.HartogsWanted
