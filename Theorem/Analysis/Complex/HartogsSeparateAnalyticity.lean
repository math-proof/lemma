/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.TietzeExtension
/-!
# Hartogs' theorem on separate analyticity

This file proves that a scalar-valued function on finite-dimensional complex Euclidean space is
holomorphic when it is holomorphic in each coordinate separately.
-/


namespace Complex.HartogsWanted

open Set Metric Filter ContinuousLinearMap

open MeasureTheory

open scoped Topology

/-- The positive logarithm of the norm of a holomorphic function satisfies the circle
sub-mean-value inequality. -/
theorem hartogs_posLog_norm_le_circleAverage {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R)) :
    Real.posLog ‖f c‖ ≤ Real.circleAverage (fun z ↦ Real.posLog ‖f z‖) c R := by
  have hf_abs : AnalyticOnNhd ℂ f (Metric.closedBall c |R|) := by
    simpa [abs_of_pos hR] using hf
  by_cases hc : ‖f c‖ ≤ 1
  · rw [(Real.posLog_eq_zero_iff _).2 (by simpa using hc)]
    exact Real.circleAverage_nonneg_of_nonneg fun _ _ ↦ Real.posLog_nonneg
  have hfc : f c ≠ 0 := fun h ↦ hc (by simp [h])
  have hlog : Real.log ‖f c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖f z‖) c R := by
    rw [hf_abs.circleAverage_log_norm hR.ne' hfc]
    simp only [le_add_iff_nonneg_left]
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ Metric.closedBall c |R|
    · refine mul_nonneg ?_ ?_
      · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf_abs u
      by_cases huc : u = c
      · simp [huc]
      apply Real.log_nonneg
      have hnorm_pos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
      apply (le_mul_inv_iff₀ hnorm_pos).2
      simpa [Metric.mem_closedBall, dist_eq_norm', abs_of_pos hR] using hu
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, hu]
  rw [Real.posLog_eq_log (by simpa using le_of_not_ge hc)]
  exact hlog.trans (Real.circleAverage_mono
    (hf_abs.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    (hf_abs.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_posLog_norm
    (fun z _ ↦ by rw [Real.posLog_apply]; exact le_max_right _ _))

theorem hartogs_exists_interior_uniform_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace F] {f : E → F → ℂ} {K : Set F} (hK : IsCompact K)
    (hz : ∀ w ∈ K, Continuous (fun z ↦ f z w))
    (hw : ∀ z, ContinuousOn (f z) K) :
    ∃ m : ℕ, (interior {z | ∀ w ∈ K, ‖f z w‖ ≤ m}).Nonempty := by
  let S : ℕ → Set E := fun m ↦ {z | ∀ w ∈ K, ‖f z w‖ ≤ m}
  have hclosed : ∀ m, IsClosed (S m) := by
    intro m
    rw [show S m = ⋂ w ∈ K, {z | ‖f z w‖ ≤ m} by ext; simp [S]]
    apply isClosed_biInter
    intro w hwK
    exact isClosed_Iic.preimage (hz w hwK).norm
  have hcover : ⋃ m, S m = univ := by
    apply Set.eq_univ_iff_forall.2
    intro z
    rcases hK.bddAbove_image (hw z).norm with ⟨C, hC⟩
    obtain ⟨m, hm⟩ := exists_nat_ge C
    apply Set.mem_iUnion.2 ⟨m, ?_⟩
    intro w hwK
    exact (hC (Set.mem_image_of_mem _ hwK)).trans hm
  simpa [S] using nonempty_interior_of_iUnion_of_closed hclosed hcover

theorem half_ball_subset_unit_ball
    {F : Type*} [NormedAddCommGroup F]
    {x : F} (hx : x ∈ closedBall 0 (1 / 2 : ℝ)) :
    closedBall x (1 / 2 : ℝ) ⊆ closedBall 0 1 := by
  intro y hy
  rw [mem_closedBall] at hx hy ⊢
  calc
    dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) + 1 / 2 := add_le_add hy hx
    _ = 1 := by norm_num

theorem quarter_ball_subset_half_ball
    {F : Type*} [NormedAddCommGroup F]
    {x : F} (hx : x ∈ closedBall 0 (1 / 4 : ℝ)) :
    x ∈ closedBall 0 (1 / 2 : ℝ) := by
  exact mem_closedBall'.2 ((mem_closedBall'.1 hx).trans (by norm_num))

theorem continuousAt_of_hartogs_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {D : E × ℂ → F} {M : ℝ} (hM : 0 ≤ M)
    (hD : ∀ z ∈ closedBall 0 (1 / 4 : ℝ), ∀ w ∈ closedBall 0 (1 / 4 : ℝ),
      ‖D (z, w) - D (0, 0)‖ ≤ 8 * M * (‖z‖ + ‖w‖)) : ContinuousAt D (0, 0) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let A : ℝ := 8 * M
  let δ : ℝ := min (1 / 4) (ε / (2 * (A + 1)))
  have hA : 0 ≤ A := mul_nonneg (by norm_num) hM
  have hden : 0 < 2 * (A + 1) := mul_pos (by norm_num) (by linarith)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  have hpmax : max ‖p.1‖ ‖p.2‖ < δ := by
    simpa only [Prod.dist_eq, Prod.fst_zero, Prod.snd_zero, dist_zero_right] using hp
  have hp₁lt : ‖p.1‖ < δ := (le_max_left _ _).trans_lt hpmax
  have hp₂lt : ‖p.2‖ < δ := (le_max_right _ _).trans_lt hpmax
  have hp₁ : p.1 ∈ closedBall 0 (1 / 4 : ℝ) := by
    rw [mem_closedBall, dist_zero_right]
    exact hp₁lt.le.trans (min_le_left _ _)
  have hp₂ : p.2 ∈ closedBall 0 (1 / 4 : ℝ) := by
    rw [mem_closedBall, dist_zero_right]
    exact hp₂lt.le.trans (min_le_left _ _)
  have hδε : δ * (2 * (A + 1)) ≤ ε :=
    (le_div_iff₀ hden).1 (min_le_right _ _)
  rw [dist_eq_norm]
  refine (hD p.1 hp₁ p.2 hp₂).trans_lt ?_
  change A * (‖p.1‖ + ‖p.2‖) < ε
  nlinarith

/-- A separately holomorphic function whose values are bounded on the product of the unit
balls is jointly complex differentiable at the center. -/
theorem differentiableAt_uncurry_of_separately_differentiable_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ → ℂ} {M : ℝ}
    (hf₁ : ∀ w, Differentiable ℂ (fun z ↦ f z w))
    (hf₂ : ∀ z, Differentiable ℂ (f z))
    (hM : ∀ z ∈ closedBall 0 1, ∀ w ∈ closedBall 0 1, ‖f z w‖ ≤ M) :
    DifferentiableAt ℂ (Function.uncurry f) (0, 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0 0)).trans (hM 0 (by simp) 0 (by simp))
  have hzeroE : (0 : E) ∈ closedBall 0 (1 / 2 : ℝ) := by simp
  have hzeroC : (0 : ℂ) ∈ closedBall 0 (1 / 2 : ℝ) := by simp
  have hline (a v : E) : HasDerivAt (fun t : ℂ ↦ a + t • v) v 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).smul_const v).const_add a
  have hlineDeriv (a v : E) (w : ℂ) :
      deriv (fun t : ℂ ↦ f (a + t • v) w) 0 =
        fderiv ℂ (fun z ↦ f z w) a v := by
    change deriv ((fun z ↦ f z w) ∘ fun t : ℂ ↦ a + t • v) 0 = _
    simpa only [zero_smul, add_zero] using
      ((hf₁ w (a + (0 : ℂ) • v)).hasFDerivAt.comp_hasDerivAt 0 (hline a v)).deriv
  have hfderiv₁ {z : E} {w : ℂ} (hz : z ∈ closedBall 0 (1 / 2 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 2 : ℝ)) :
      ‖fderiv ℂ (fun x ↦ f x w) z‖ ≤ 2 * M := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hM0)
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let u : E := (‖v‖ : ℂ)⁻¹ • v
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hvpos.ne']
    have hv_eq : v = (‖v‖ : ℂ) • u := by
      simp [u, hvpos.ne']
    have hdiff : Differentiable ℂ (fun t : ℂ ↦ f (z + t • u) w) :=
      (hf₁ w).comp (by fun_prop)
    have hbound : ‖deriv (fun t : ℂ ↦ f (z + t • u) w) 0‖ ≤ 2 * M := by
      calc
        _ ≤ M / (1 / 2 : ℝ) :=
          Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
            hdiff.diffContOnCl fun t ht ↦ by
              apply hM (z + t • u)
              · apply half_ball_subset_unit_ball hz
                have htq : ‖t‖ = 1 / 2 := by
                  simpa [mem_sphere, dist_zero_right] using ht
                simp [mem_closedBall, dist_eq_norm, norm_smul, hunorm, htq]
              · exact half_ball_subset_unit_ball hw (by simp)
        _ = 2 * M := by ring
    rw [hlineDeriv] at hbound
    have hscale : fderiv ℂ (fun x ↦ f x w) z v =
        (‖v‖ : ℂ) • fderiv ℂ (fun x ↦ f x w) z u := by
      calc
        _ = fderiv ℂ (fun x ↦ f x w) z ((‖v‖ : ℂ) • u) := congrArg _ hv_eq
        _ = _ := map_smul _ _ _
    calc
      ‖fderiv ℂ (fun x ↦ f x w) z v‖ =
          ‖(‖v‖ : ℂ)‖ * ‖fderiv ℂ (fun x ↦ f x w) z u‖ := by
        rw [hscale, norm_smul]
      _ = ‖v‖ * ‖fderiv ℂ (fun x ↦ f x w) z u‖ := by simp
      _ ≤ ‖v‖ * (2 * M) := mul_le_mul_of_nonneg_left hbound (norm_nonneg v)
      _ = 2 * M * ‖v‖ := by ring
  have hderiv₂ {z : E} {w : ℂ} (hz : z ∈ closedBall 0 (1 / 2 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 2 : ℝ)) :
      ‖deriv (f z) w‖ ≤ 2 * M := by
    calc
      ‖deriv (f z) w‖ ≤ M / (1 / 2 : ℝ) :=
        Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
          (hf₂ z).diffContOnCl fun x hx ↦ hM z (half_ball_subset_unit_ball hz (by simp)) x
            (half_ball_subset_unit_ball hw (sphere_subset_closedBall hx))
      _ = 2 * M := by ring
  have hvalue₁ {z z' : E} {w : ℂ}
      (hz : z ∈ closedBall 0 (1 / 2 : ℝ))
      (hz' : z' ∈ closedBall 0 (1 / 2 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 2 : ℝ)) :
      ‖f z w - f z' w‖ ≤ 2 * M * ‖z - z'‖ := by
    exact (convex_closedBall (0 : E) (1 / 2 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ ↦ hf₁ w x) (fun x hx ↦ hfderiv₁ hx hw) hz' hz
  have hvalue₂ {z : E} {w w' : ℂ}
      (hz : z ∈ closedBall 0 (1 / 2 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 2 : ℝ))
      (hw' : w' ∈ closedBall 0 (1 / 2 : ℝ)) :
      ‖f z w - f z w'‖ ≤ 2 * M * ‖w - w'‖ := by
    simpa [dist_eq_norm] using
      (convex_closedBall (0 : ℂ) (1 / 2 : ℝ)).norm_image_sub_le_of_norm_deriv_le
        (f := f z) (x := w') (y := w) (fun x _ ↦ hf₂ z x)
        (fun x hx ↦ hderiv₂ hz hx) hw' hw
  have hD₁ {z : E} {w : ℂ} (hz : z ∈ closedBall 0 (1 / 4 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 4 : ℝ)) :
      ‖fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0‖ ≤
        8 * M * (‖z‖ + ‖w‖) := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (by norm_num) hM0) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let u : E := (‖v‖ : ℂ)⁻¹ • v
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hvpos.ne']
    have hv_eq : v = (‖v‖ : ℂ) • u := by
      simp [u, hvpos.ne']
    let g : ℂ → ℂ := fun t ↦ f (z + t • u) w - f (t • u) 0
    have hg : Differentiable ℂ g := by
      dsimp [g]
      exact ((hf₁ w).comp (by fun_prop)).sub ((hf₁ 0).comp (by fun_prop))
    have hgbound (t : ℂ) (ht : t ∈ sphere 0 (1 / 4 : ℝ)) :
        ‖g t‖ ≤ 2 * M * (‖z‖ + ‖w‖) := by
      have htq : ‖t‖ = 1 / 4 := by simpa [mem_sphere, dist_eq_norm] using ht
      have htu : t • u ∈ closedBall (0 : E) (1 / 4 : ℝ) := by
        rw [mem_closedBall, dist_zero_right, norm_smul, hunorm, mul_one, htq]
      have hztu : z + t • u ∈ closedBall (0 : E) (1 / 2 : ℝ) := by
        rw [mem_closedBall, dist_zero_right] at hz ⊢
        calc
          ‖z + t • u‖ ≤ ‖z‖ + ‖t • u‖ := norm_add_le _ _
          _ ≤ (1 / 4 : ℝ) + 1 / 4 := add_le_add hz (by simpa [mem_closedBall] using htu)
          _ = 1 / 2 := by norm_num
      have htu' := quarter_ball_subset_half_ball htu
      have hw' := quarter_ball_subset_half_ball hw
      calc
        ‖g t‖ ≤ ‖f (z + t • u) w - f (z + t • u) 0‖ +
            ‖f (z + t • u) 0 - f (t • u) 0‖ := by
          dsimp [g]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * M * ‖w‖ + 2 * M * ‖z‖ := by
          gcongr
          · simpa using hvalue₂ hztu hw' hzeroC
          · simpa using hvalue₁ hztu htu' hzeroC
        _ = 2 * M * (‖z‖ + ‖w‖) := by ring
    have hderiv : ‖deriv g 0‖ ≤ 8 * M * (‖z‖ + ‖w‖) := by
      calc
        _ ≤ (2 * M * (‖z‖ + ‖w‖)) / (1 / 4 : ℝ) :=
          Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (by norm_num)
            hg.diffContOnCl hgbound
        _ = 8 * M * (‖z‖ + ‖w‖) := by ring
    have hgderiv : deriv g 0 =
        (fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0) u := by
      rw [show deriv g 0 = deriv (fun t : ℂ ↦ f (z + t • u) w) 0 -
          deriv (fun t : ℂ ↦ f (t • u) 0) 0 by
        exact deriv_sub (((hf₁ w).comp (by fun_prop)) 0) (((hf₁ 0).comp (by fun_prop)) 0)]
      rw [hlineDeriv z u w]
      simpa using hlineDeriv (0 : E) u 0
    rw [hgderiv] at hderiv
    have hscale :
        (fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0) v =
          (‖v‖ : ℂ) • (fderiv ℂ (fun x ↦ f x w) z -
            fderiv ℂ (fun x ↦ f x 0) 0) u := by
      calc
        _ = (fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0)
            ((‖v‖ : ℂ) • u) := congrArg _ hv_eq
        _ = _ := map_smul _ _ _
    calc
      ‖(fderiv ℂ (fun x ↦ f x w) z - fderiv ℂ (fun x ↦ f x 0) 0) v‖ =
          ‖(‖v‖ : ℂ)‖ * ‖(fderiv ℂ (fun x ↦ f x w) z -
            fderiv ℂ (fun x ↦ f x 0) 0) u‖ := by
        rw [hscale, norm_smul]
      _ = ‖v‖ * ‖(fderiv ℂ (fun x ↦ f x w) z -
            fderiv ℂ (fun x ↦ f x 0) 0) u‖ := by simp
      _ ≤ ‖v‖ * (8 * M * (‖z‖ + ‖w‖)) :=
        mul_le_mul_of_nonneg_left hderiv (norm_nonneg v)
      _ = 8 * M * (‖z‖ + ‖w‖) * ‖v‖ := by ring
  have hD₂ {z : E} {w : ℂ} (hz : z ∈ closedBall 0 (1 / 4 : ℝ))
      (hw : w ∈ closedBall 0 (1 / 4 : ℝ)) :
      ‖deriv (f z) w - deriv (f 0) 0‖ ≤ 8 * M * (‖z‖ + ‖w‖) := by
    let g : ℂ → ℂ := fun t ↦ f z (w + t) - f 0 t
    have hg : Differentiable ℂ g := by
      dsimp [g]
      exact ((hf₂ z).comp (by fun_prop)).sub (hf₂ 0)
    have hgbound (t : ℂ) (ht : t ∈ sphere 0 (1 / 4 : ℝ)) :
        ‖g t‖ ≤ 2 * M * (‖z‖ + ‖w‖) := by
      have htq : ‖t‖ = 1 / 4 := by simpa [mem_sphere, dist_eq_norm] using ht
      have ht' : t ∈ closedBall (0 : ℂ) (1 / 2 : ℝ) := by
        rw [mem_closedBall, dist_zero_right, htq]
        norm_num
      have hwt : w + t ∈ closedBall (0 : ℂ) (1 / 2 : ℝ) := by
        rw [mem_closedBall, dist_zero_right] at hw ⊢
        calc
          ‖w + t‖ ≤ ‖w‖ + ‖t‖ := norm_add_le _ _
          _ ≤ (1 / 4 : ℝ) + 1 / 4 := add_le_add hw htq.le
          _ = 1 / 2 := by norm_num
      have hz' := quarter_ball_subset_half_ball hz
      calc
        ‖g t‖ ≤ ‖f z (w + t) - f z t‖ + ‖f z t - f 0 t‖ := by
          dsimp [g]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * M * ‖w‖ + 2 * M * ‖z‖ := by
          gcongr
          · simpa using hvalue₂ hz' hwt ht'
          · simpa using hvalue₁ hz' hzeroE ht'
        _ = 2 * M * (‖z‖ + ‖w‖) := by ring
    have hderiv : ‖deriv g 0‖ ≤ 8 * M * (‖z‖ + ‖w‖) := by
      calc
        _ ≤ (2 * M * (‖z‖ + ‖w‖)) / (1 / 4 : ℝ) :=
          Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (by norm_num)
            hg.diffContOnCl hgbound
        _ = 8 * M * (‖z‖ + ‖w‖) := by ring
    have hgderiv : deriv g 0 = deriv (f z) w - deriv (f 0) 0 := by
      rw [show deriv g 0 = deriv (fun t : ℂ ↦ f z (w + t)) 0 - deriv (f 0) 0 by
        exact deriv_sub (((hf₂ z).comp (by fun_prop)) 0) (hf₂ 0 0)]
      have hlinew : HasDerivAt (fun t : ℂ ↦ w + t) 1 0 :=
        (hasDerivAt_id (𝕜 := ℂ) (x := 0)).const_add w
      have hcomp := (hf₂ z (w + 0)).hasDerivAt.comp 0 hlinew
      have hcomp' : deriv (fun t : ℂ ↦ f z (w + t)) 0 = deriv (f z) w := by
        change deriv ((f z) ∘ fun t : ℂ ↦ w + t) 0 = _
        simpa only [add_zero, mul_one] using hcomp.deriv
      rw [hcomp']
    rwa [hgderiv] at hderiv
  let f₁ : E → ℂ → E →L[ℂ] ℂ := fun z w ↦ fderiv ℂ (fun x ↦ f x w) z
  let D₂ : E × ℂ → ℂ := fun p ↦ deriv (f p.1) p.2
  let f₂ : E → ℂ → ℂ →L[ℂ] ℂ := fun z w ↦ fderiv ℂ (f z) w
  have hf₁c : ContinuousAt (Function.uncurry f₁) (0, 0) := by
    apply continuousAt_of_hartogs_bound hM0
    intro z hz w hw
    exact hD₁ hz hw
  have hD₂c : ContinuousAt D₂ (0, 0) := by
    apply continuousAt_of_hartogs_bound hM0
    intro z hz w hw
    exact hD₂ hz hw
  have hf₂c : ContinuousAt (Function.uncurry f₂) (0, 0) := by
    rw [show Function.uncurry f₂ = fun p ↦ toSpanSingleton ℂ (D₂ p) by
      funext p
      exact (toSpanSingleton_deriv (f := f p.1) (x := p.2)).symm]
    exact (toSpanSingletonLIE ℂ ℂ).continuous.continuousAt.comp' hD₂c
  exact (hasStrictFDerivAt_uncurry_coprod
    (f₁ := f₁) (f₂ := f₂)
    (Eventually.of_forall fun p ↦ (hf₁ p.2 p.1).hasFDerivAt)
    (Eventually.of_forall fun p ↦ (hf₂ p.1 p.2).hasFDerivAt)
    hf₁c hf₂c).differentiableAt

/-- A separately holomorphic function that is bounded on a product of open neighborhoods is
jointly complex differentiable at every point of that product. -/
theorem differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ → ℂ} {U : Set E} {V : Set ℂ} {M : ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf₁ : ∀ w, Differentiable ℂ (fun z ↦ f z w))
    (hf₂ : ∀ z, Differentiable ℂ (f z))
    (hM : ∀ z ∈ U, ∀ w ∈ V, ‖f z w‖ ≤ M)
    {z₀ : E} (hz₀ : z₀ ∈ U) {w₀ : ℂ} (hw₀ : w₀ ∈ V) :
    DifferentiableAt ℂ (Function.uncurry f) (z₀, w₀) := by
  obtain ⟨az, haz, hballz⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  obtain ⟨aw, haw, hballw⟩ := Metric.isOpen_iff.1 hV w₀ hw₀
  let rz : ℝ := az / 2
  let rw : ℝ := aw / 2
  have hrz : 0 < rz := div_pos haz (by norm_num)
  have hrw : 0 < rw := div_pos haw (by norm_num)
  let g : E → ℂ → ℂ := fun z w ↦
    f (z₀ + (rz : ℂ) • z) (w₀ + (rw : ℂ) * w)
  have hg₁ : ∀ w, Differentiable ℂ (fun z ↦ g z w) := by
    intro w
    apply (hf₁ _).comp
    fun_prop
  have hg₂ : ∀ z, Differentiable ℂ (g z) := by
    intro z
    apply (hf₂ _).comp
    fun_prop
  have hgM : ∀ z ∈ closedBall 0 1, ∀ w ∈ closedBall 0 1, ‖g z w‖ ≤ M := by
    intro z hz w hw
    apply hM
    · apply hballz
      rw [mem_ball, dist_eq_norm]
      have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz
      have hscaled : rz * ‖z‖ ≤ rz := by
        simpa using mul_le_mul_of_nonneg_left hz' hrz.le
      have hlt : rz * ‖z‖ < az :=
        hscaled.trans_lt (by dsimp [rz]; linarith)
      simpa [g, rz, norm_smul, abs_of_pos haz] using hlt
    · apply hballw
      rw [mem_ball, dist_eq_norm]
      have hw' : ‖w‖ ≤ 1 := by simpa [mem_closedBall] using hw
      have hscaled : rw * ‖w‖ ≤ rw := by
        simpa using mul_le_mul_of_nonneg_left hw' hrw.le
      have hlt : rw * ‖w‖ < aw :=
        hscaled.trans_lt (by dsimp [rw]; linarith)
      simpa [g, rw, norm_mul, abs_of_pos haw] using hlt
  have hg :=
    differentiableAt_uncurry_of_separately_differentiable_of_bounded hg₁ hg₂ hgM
  let H : E × ℂ → E × ℂ := fun p ↦
    (((rz : ℂ)⁻¹ • (p.1 - z₀)), (rw : ℂ)⁻¹ * (p.2 - w₀))
  have hH : Differentiable ℂ H := by
    dsimp [H]
    fun_prop
  have hH₀ : H (z₀, w₀) = (0, 0) := by simp [H]
  have hgH : DifferentiableAt ℂ (Function.uncurry g) (H (z₀, w₀)) := by
    rw [hH₀]
    exact hg
  have hcomp := hgH.comp (z₀, w₀) (hH (z₀, w₀))
  convert hcomp using 1
  funext p
  dsimp [Function.uncurry, g, H]
  simp only [ne_eq, Complex.ofReal_eq_zero, hrw.ne', not_false_eq_true,
    mul_inv_cancel_left₀, add_sub_cancel]
  rw [← IsScalarTower.smul_assoc]
  simp [Algebra.smul_def, hrz.ne']

/-- On a bounded product, the Cauchy coefficients in the scalar variable are holomorphic in the
finite-dimensional block variable on a smaller ball. -/
theorem differentiableOn_cauchyCoefficient_of_separately_differentiable_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {f : E → ℂ → ℂ} {z₀ : E} {w₀ : ℂ} {A B M : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hf₁ : ∀ w, Differentiable ℂ (fun z ↦ f z w))
    (hf₂ : ∀ z, Differentiable ℂ (f z))
    (hM : ∀ z ∈ closedBall z₀ A, ∀ w ∈ closedBall w₀ B, ‖f z w‖ ≤ M)
    (k : ℕ) :
    DifferentiableOn ℂ
      (fun z ↦ (cauchyPowerSeries (f z) w₀ (B / 2) k) (fun _ ↦ 1))
      (ball z₀ (A / 2)) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hM0 : 0 ≤ M :=
    (norm_nonneg (f z₀ w₀)).trans
      (hM z₀ (by simp [hA.le]) w₀ (by simp [hB.le]))
  let S : Set (E × ℂ) :=
    closedBall z₀ (A / 2) ×ˢ closedBall w₀ (3 * B / 4)
  have hSclosed : IsClosed S := isClosed_closedBall.prod isClosed_closedBall
  have hjoint : DifferentiableOn ℂ (Function.uncurry f)
      (ball z₀ A ×ˢ ball w₀ B) := by
    intro p hp
    exact
      (differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded
        isOpen_ball isOpen_ball hf₁ hf₂
        (fun z hz w hw ↦ hM z (ball_subset_closedBall hz) w
          (ball_subset_closedBall hw)) hp.1 hp.2).differentiableWithinAt
  have hSsub : S ⊆ ball z₀ A ×ˢ ball w₀ B := by
    intro p hp
    constructor
    · exact (mem_closedBall.1 hp.1).trans_lt (by linarith)
    · exact (mem_closedBall.1 hp.2).trans_lt (by linarith)
  have hcontS : ContinuousOn (Function.uncurry f) S :=
    hjoint.continuousOn.mono hSsub
  let fc : C(S, ℂ) := ⟨S.domRestrict (Function.uncurry f), hcontS.domRestrict⟩
  let fre : C(S, ℝ) :=
    ⟨fun p ↦ (fc p).re, Complex.continuous_re.comp fc.continuous⟩
  let fim : C(S, ℝ) :=
    ⟨fun p ↦ (fc p).im, Complex.continuous_im.comp fc.continuous⟩
  obtain ⟨gre, hgre⟩ := ContinuousMap.exists_restrict_eq hSclosed fre
  obtain ⟨gim, hgim⟩ := ContinuousMap.exists_restrict_eq hSclosed fim
  let G : E × ℂ → ℂ := fun p ↦
    (gre p : ℂ) + Complex.I * (gim p : ℂ)
  have hGc : Continuous G := by
    dsimp [G]
    fun_prop
  have hGeq : ∀ p ∈ S, G p = Function.uncurry f p := by
    intro p hp
    apply Complex.ext
    · have h := DFunLike.congr_fun hgre ⟨p, hp⟩
      simpa [G, fre, fc] using h
    · have h := DFunLike.congr_fun hgim ⟨p, hp⟩
      simpa [G, fim, fc] using h
  let s : ℝ := B / 2
  have hs : 0 < s := div_pos hB (by norm_num)
  have hcircle_ne (t : ℝ) : circleMap 0 s t ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_circleMap_zero, abs_of_pos hs]
    exact hs.ne'
  let weight : ℝ → ℂ := fun t ↦
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (circleMap 0 s t * Complex.I) *
      ((circleMap 0 s t)⁻¹ ^ k * (circleMap 0 s t)⁻¹)
  have hweight : Continuous weight := by
    dsimp [weight]
    fun_prop (disch := aesop)
  let b : E → ℂ := fun z ↦
    (cauchyPowerSeries (fun w ↦ G (z, w)) w₀ s k) (fun _ ↦ 1)
  have hb_eq (z : E) : b z =
      ∫ t in Icc 0 (2 * Real.pi), weight t * G (z, circleMap w₀ s t) := by
    dsimp [b]
    rw [cauchyPowerSeries_apply, circleIntegral_def_Icc]
    simp only [deriv_circleMap, circleMap_sub_center, one_div, smul_eq_mul]
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [weight]
    ring
  have hwcircle (t : ℝ) : circleMap w₀ s t ∈ closedBall w₀ (3 * B / 4) := by
    rw [mem_closedBall]
    have ht := circleMap_mem_sphere w₀ hs.le t
    rw [mem_sphere] at ht
    rw [ht]
    dsimp [s]
    linarith
  have hGeq_nhds {z : E} (hz : z ∈ ball z₀ (A / 2)) (t : ℝ) :
      (fun x ↦ G (x, circleMap w₀ s t)) =ᶠ[nhds z]
        (fun x ↦ f x (circleMap w₀ s t)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx
    exact hGeq _ ⟨ball_subset_closedBall hx, hwcircle t⟩
  have hlineDeriv (z v : E) (w : ℂ) :
      deriv (fun t : ℂ ↦ f (z + t • v) w) 0 =
        fderiv ℂ (fun x ↦ f x w) z v := by
    have hline : HasDerivAt (fun t : ℂ ↦ z + t • v) v 0 := by
      simpa using
        ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).smul_const v).const_add z
    change deriv ((fun x ↦ f x w) ∘ fun t : ℂ ↦ z + t • v) 0 = _
    simpa only [zero_smul, add_zero] using
      ((hf₁ w (z + (0 : ℂ) • v)).hasFDerivAt.comp_hasDerivAt 0 hline).deriv
  let L : ℝ := M / (A / 2)
  have hL : 0 ≤ L := div_nonneg hM0 (by positivity)
  have hfderiv_bound {z : E} (hz : z ∈ ball z₀ (A / 2))
      {w : ℂ} (hw : w ∈ closedBall w₀ B) :
      ‖fderiv ℂ (fun x ↦ f x w) z‖ ≤ L := by
    apply ContinuousLinearMap.opNorm_le_bound _ hL
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let u : E := (‖v‖ : ℂ)⁻¹ • v
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hunorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hvpos.ne']
    have hv_eq : v = (‖v‖ : ℂ) • u := by
      simp [u, hvpos.ne']
    have hdiff : Differentiable ℂ (fun t : ℂ ↦ f (z + t • u) w) :=
      (hf₁ w).comp (by fun_prop)
    have hbound : ‖deriv (fun t : ℂ ↦ f (z + t • u) w) 0‖ ≤ L := by
      apply
        (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
          (div_pos hA (by norm_num)) hdiff.diffContOnCl ?_)
      intro t ht
      apply hM (z + t • u)
      · rw [mem_closedBall]
        have htq : ‖t‖ = A / 2 := by
          simpa [mem_sphere, dist_zero_right] using ht
        calc
          dist (z + t • u) z₀ ≤ dist (z + t • u) z + dist z z₀ :=
            dist_triangle _ _ _
          _ = ‖t‖ + dist z z₀ := by
            simp [dist_eq_norm, norm_smul, hunorm]
          _ ≤ A := by
            have hz' := mem_ball.1 hz
            linarith
      · exact hw
    rw [hlineDeriv] at hbound
    have hscale : fderiv ℂ (fun x ↦ f x w) z v =
        (‖v‖ : ℂ) • fderiv ℂ (fun x ↦ f x w) z u := by
      calc
        _ = fderiv ℂ (fun x ↦ f x w) z ((‖v‖ : ℂ) • u) :=
          congrArg _ hv_eq
        _ = _ := map_smul _ _ _
    rw [hscale, norm_smul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hbound (norm_nonneg v)
  let g : ℂ → E → ℂ := fun w z ↦ G (z, w)
  have hgcont : Continuous (Function.uncurry g) := by
    change Continuous (fun p : ℂ × E ↦ G (p.2, p.1))
    exact hGc.comp (by fun_prop)
  have hfdmeas : Measurable (fun p : ℂ × E ↦ fderiv ℂ (g p.1) p.2) :=
    measurable_fderiv_with_param ℂ hgcont
  let J : E → ℂ := fun z ↦
    ∫ t in Icc 0 (2 * Real.pi), weight t * G (z, circleMap w₀ s t)
  have hJ : DifferentiableOn ℂ J (ball z₀ (A / 2)) := by
    intro z hz
    let F : E → ℝ → ℂ := fun x t ↦
      weight t * G (x, circleMap w₀ s t)
    let F' : E → ℝ → E →L[ℂ] ℂ := fun x t ↦
      weight t • fderiv ℂ (g (circleMap w₀ s t)) x
    let bound : ℝ → ℝ := fun t ↦ ‖weight t‖ * L
    have hFcont (x : E) : Continuous (F x) := by
      dsimp [F]
      exact hweight.mul (hGc.comp (by fun_prop))
    have hF'_meas :
        AEStronglyMeasurable (F' z) (volume.restrict (Icc 0 (2 * Real.pi))) := by
      apply Measurable.aestronglyMeasurable
      dsimp [F']
      apply hweight.measurable.smul
      simpa [Function.comp_def] using hfdmeas.comp
        (Measurable.prod (f := fun t : ℝ ↦ (circleMap w₀ s t, z))
          (continuous_circleMap w₀ s).measurable measurable_const)
    have hbound_int :
        Integrable bound (volume.restrict (Icc 0 (2 * Real.pi))) := by
      apply Continuous.integrableOn_Icc
      dsimp [bound]
      exact hweight.norm.mul continuous_const
    have hparam := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (isOpen_ball.mem_nhds hz)
      (Eventually.of_forall fun x ↦ (hFcont x).aestronglyMeasurable)
      ((hFcont z).integrableOn_Icc) hF'_meas (bound := bound)
      (by
        filter_upwards with t x hx
        dsimp [F', bound]
        have hfd_eq : fderiv ℂ (g (circleMap w₀ s t)) x =
            fderiv ℂ (fun y ↦ f y (circleMap w₀ s t)) x :=
          (hGeq_nhds hx t).fderiv_eq
        rw [norm_smul, hfd_eq]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply hfderiv_bound hx
        rw [mem_closedBall]
        have ht := circleMap_mem_sphere w₀ hs.le t
        rw [mem_sphere] at ht
        rw [ht]
        dsimp [s]
        linarith)
      hbound_int
      (by
        filter_upwards with t x hx
        dsimp [F, F']
        have hGderiv :=
          (hf₁ (circleMap w₀ s t) x).hasFDerivAt.congr_of_eventuallyEq
            (hGeq_nhds hx t)
        have hfd_eq : fderiv ℂ (g (circleMap w₀ s t)) x =
            fderiv ℂ (fun y ↦ f y (circleMap w₀ s t)) x :=
          (hGeq_nhds hx t).fderiv_eq
        rw [hfd_eq]
        exact hGderiv.const_mul (weight t))
    have hJeq : J = fun x ↦ ∫ t in Icc 0 (2 * Real.pi), F x t := by
      rfl
    rw [hJeq]
    exact hparam.differentiableAt.differentiableWithinAt
  have hab : ∀ z ∈ ball z₀ (A / 2),
      (cauchyPowerSeries (f z) w₀ s k) (fun _ ↦ 1) = b z := by
    intro z hz
    dsimp [b]
    rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply]
    congr 1
    apply circleIntegral.integral_congr hs.le
    intro w hw
    have hwS : w ∈ closedBall w₀ (3 * B / 4) := by
      rw [mem_closedBall]
      have hw' := mem_sphere.1 hw
      rw [hw']
      dsimp [s]
      linarith
    dsimp
    rw [hGeq (z, w) ⟨ball_subset_closedBall hz, hwS⟩]
    rfl
  have hbJ : b = J := funext hb_eq
  rw [hbJ] at hab
  exact hJ.congr hab

/-- Cauchy's estimate for a scalar Taylor coefficient, stated for Mathlib's
`cauchyPowerSeries`. -/
theorem norm_cauchyCoefficient_le
    {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : Differentiable ℂ f)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖(cauchyPowerSeries f c R).coeff k‖ ≤ M * R⁻¹ ^ k := by
  have hcont : Continuous (fun θ : ℝ ↦ ‖f (circleMap c R θ)‖) :=
    hf.continuous.norm.comp (continuous_circleMap c R)
  have hint :
      (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap c R θ)‖) ≤
        ∫ _θ : ℝ in 0..2 * Real.pi, M := by
    apply intervalIntegral.integral_mono_on Real.two_pi_pos.le
      (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    intro θ _hθ
    exact hM _ (circleMap_mem_sphere c hR.le θ)
  have hseries := norm_cauchyPowerSeries_le f c R k
  have heval : ‖(cauchyPowerSeries f c R).coeff k‖ ≤
      ‖cauchyPowerSeries f c R k‖ := by
    rw [FormalMultilinearSeries.coeff]
    calc
      _ ≤ ‖cauchyPowerSeries f c R k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        (cauchyPowerSeries f c R k).le_opNorm (fun _ ↦ 1)
      _ = _ := by simp
  calc
    ‖(cauchyPowerSeries f c R).coeff k‖ ≤
        ‖cauchyPowerSeries f c R k‖ := heval
    _ ≤ ((2 * Real.pi)⁻¹ *
          ∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap c R θ)‖) *
        |R|⁻¹ ^ k := hseries
    _ ≤ ((2 * Real.pi)⁻¹ * (2 * Real.pi * M)) * R⁻¹ ^ k := by
      rw [abs_of_pos hR]
      gcongr
      simpa using hint
    _ = M * R⁻¹ ^ k := by
      field_simp [Real.pi_ne_zero]

lemma disk_integral_eq_polar {u : ℂ → ℝ} (hu : Continuous u)
    {R : ℝ} (_hR : 0 ≤ R) :
    ∫ z in closedBall (0 : ℂ) R, u z =
      ∫ r in Ioc 0 R, ∫ θ in Ioo (-Real.pi) Real.pi,
        r * u (Complex.polarCoord.symm (r, θ)) := by
  rw [← integral_indicator measurableSet_closedBall]
  rw [← Complex.integral_comp_polarCoord_symm]
  rw [polarCoord_target]
  have hint : IntegrableOn
      (fun p : ℝ × ℝ ↦ p.1 * u (Complex.polarCoord.symm p))
      (Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi) := by
    have hpolar : Continuous (fun p : ℝ × ℝ ↦
        Complex.polarCoord.symm p) := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    have hbig : IntegrableOn
        (fun p : ℝ × ℝ ↦ p.1 * u (Complex.polarCoord.symm p))
        (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi) :=
      ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
        ((continuous_fst.mul (hu.comp hpolar)).continuousOn)
    exact hbig.mono_set fun _ hp ↦
      ⟨Ioc_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩
  rw [Measure.volume_eq_prod]
  rw [← setIntegral_prod _ hint]
  rw [← integral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  rw [← integral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
  congr 1
  funext p
  by_cases hpθ : p.2 ∈ Ioo (-Real.pi) Real.pi
  · by_cases hpr : 0 < p.1
    · by_cases hpR : p.1 ≤ R
      · have habs : |p.1| ≤ R := by simpa [abs_of_pos hpr] using hpR
        simp [hpr, hpR, hpθ, habs, smul_eq_mul]
      · have habs : ¬|p.1| ≤ R := by simpa [abs_of_pos hpr] using hpR
        simp [hpr, hpR, hpθ, habs]
    · have hpnonpos : p.1 ≤ 0 := le_of_not_gt hpr
      have hpnot : p.1 ∉ Ioc 0 R := by simp [hpnonpos]
      simp [hpr, hpnot]
  · simp [hpθ]

lemma angular_integral_eq_circleAverage (u : ℂ → ℝ) (r : ℝ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, u (Complex.polarCoord.symm (r, θ)) =
      2 * Real.pi * Real.circleAverage u 0 r := by
  rw [MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc]
  rw [← intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  have hfun : (fun θ : ℝ ↦ u (Complex.polarCoord.symm (r, θ))) =
      fun θ : ℝ ↦ u (circleMap 0 r θ) := by
    funext θ
    congr 1
    simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  rw [hfun]
  rw [Real.circleAverage_eq_integral_add (f := u) (c := 0) (R := r) (-Real.pi)]
  have hshift :
      (∫ θ : ℝ in 0..2 * Real.pi, u (circleMap 0 r (θ + -Real.pi))) =
        ∫ θ : ℝ in -Real.pi..Real.pi, u (circleMap 0 r θ) := by
    have h := intervalIntegral.integral_comp_add_right
      (fun θ : ℝ ↦ u (circleMap 0 r θ)) (-Real.pi)
        (a := 0) (b := 2 * Real.pi)
    rw [zero_add, show 2 * Real.pi + -Real.pi = Real.pi by ring] at h
    exact h
  rw [hshift]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

lemma disk_integral_eq_polar_closed {u : ℂ → ℝ} (hu : Continuous u)
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ z in closedBall (0 : ℂ) R, u z =
      ∫ r in Ioc 0 R, ∫ θ in Icc (-Real.pi) Real.pi,
        r * u (Complex.polarCoord.symm (r, θ)) := by
  rw [disk_integral_eq_polar hu hR]
  congr 1
  funext r
  exact MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Icc

lemma disk_submean_zero {u : ℂ → ℝ} (hu : Continuous u)
    {R : ℝ} (hR : 0 < R)
    (hsub : ∀ r ∈ Ioc 0 R, u 0 ≤ Real.circleAverage u 0 r) :
    (volume (closedBall (0 : ℂ) R)).toReal * u 0 ≤
      ∫ z in closedBall (0 : ℂ) R, u z := by
  have hconst : (volume (closedBall (0 : ℂ) R)).toReal * u 0 =
      ∫ r in Ioc 0 R, 2 * Real.pi * r * u 0 := by
    have h := disk_integral_eq_polar_closed
      (u := fun _ : ℂ ↦ u 0) continuous_const hR.le
    have hangle (r : ℝ) :
        (∫ θ in Icc (-Real.pi) Real.pi, r * (u 0 : ℝ)) =
          2 * Real.pi * r * u 0 := by
      rw [← MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Icc]
      rw [MeasureTheory.integral_const_mul]
      have hc : (∫ θ in Ioo (-Real.pi) Real.pi, (u 0 : ℝ)) =
          2 * Real.pi * u 0 := by
        simpa only [Real.circleAverage_const] using
          angular_integral_eq_circleAverage (fun _ : ℂ ↦ u 0) r
      rw [hc]
      ring
    simp_rw [hangle] at h
    rw [MeasureTheory.setIntegral_const] at h
    simpa only [smul_eq_mul, measureReal_def, mul_assoc] using h
  rw [hconst, disk_integral_eq_polar_closed hu hR.le]
  apply MeasureTheory.setIntegral_mono_on
  · exact
      (show Continuous (fun r : ℝ ↦ 2 * Real.pi * r * u 0) by fun_prop).continuousOn
        |>.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  · have hcontinuous : Continuous (fun r : ℝ ↦
        ∫ θ in Icc (-Real.pi) Real.pi,
          r * u (Complex.polarCoord.symm (r, θ))) := by
      apply continuous_parametric_integral_of_continuous
      · change Continuous (fun p : ℝ × ℝ ↦
          p.1 * u (Complex.polarCoord.symm p))
        have hpolar : Continuous (fun p : ℝ × ℝ ↦
            Complex.polarCoord.symm p) := by
          simp only [Complex.polarCoord_symm_apply]
          fun_prop
        exact continuous_fst.mul (hu.comp hpolar)
      · exact isCompact_Icc
    exact hcontinuous.continuousOn.integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  · exact measurableSet_Ioc
  · intro r hr
    rw [← MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Icc]
    rw [MeasureTheory.integral_const_mul]
    rw [angular_integral_eq_circleAverage]
    have hr0 : 0 ≤ r := hr.1.le
    have hpi : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
    calc
      2 * Real.pi * r * u 0 = (2 * Real.pi * r) * u 0 := by ring
      _ ≤ (2 * Real.pi * r) * Real.circleAverage u 0 r :=
        mul_le_mul_of_nonneg_left (hsub r hr) (mul_nonneg hpi hr0)
      _ = r * (2 * Real.pi * Real.circleAverage u 0 r) := by ring

lemma diskIntegral_add_center (u : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    ∫ t in closedBall (0 : ℂ) R, u (t + c) =
      ∫ z in closedBall c R, u z := by
  have hfun : (closedBall (0 : ℂ) R).indicator (fun t ↦ u (t + c)) =
      fun t ↦ (closedBall c R).indicator u (t + c) := by
    funext t
    by_cases ht : t ∈ closedBall (0 : ℂ) R
    · have htc : t + c ∈ closedBall c R := by
        simpa [mem_closedBall, dist_eq_norm] using ht
      simp [ht, htc]
    · have htc : t + c ∉ closedBall c R := by
        simpa [mem_closedBall, dist_eq_norm] using ht
      simp [ht, htc]
  calc
    _ = ∫ t, (closedBall (0 : ℂ) R).indicator (fun x ↦ u (x + c)) t := by
      rw [MeasureTheory.integral_indicator measurableSet_closedBall]
    _ = ∫ t, (closedBall c R).indicator u (t + c) := by rw [hfun]
    _ = ∫ z, (closedBall c R).indicator u z :=
      MeasureTheory.integral_add_right_eq_self _ c
    _ = _ := MeasureTheory.integral_indicator measurableSet_closedBall

lemma disk_submean {u : ℂ → ℝ} (hu : Continuous u)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : ∀ r ∈ Ioc 0 R, u c ≤ Real.circleAverage u c r) :
    (volume (closedBall c R)).toReal * u c ≤
      ∫ z in closedBall c R, u z := by
  let v : ℂ → ℝ := fun t ↦ u (t + c)
  have hv : Continuous v := hu.comp (continuous_id.add continuous_const)
  have hvsub : ∀ r ∈ Ioc 0 R, v 0 ≤ Real.circleAverage v 0 r := by
    intro r hr
    simpa [v, Real.circleAverage_map_add_const] using hsub r hr
  have h := disk_submean_zero hv hR hvsub
  rw [diskIntegral_add_center u c R] at h
  simpa [v, Complex.volume_closedBall] using h

end Complex.HartogsWanted
