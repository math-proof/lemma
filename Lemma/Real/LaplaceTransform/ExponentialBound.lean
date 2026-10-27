import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.LaplaceTransform.Basic
open MeasureTheory Set Real Filter Topology Asymptotics
open-positive-ray (piecewise continuity on `ℝ_{>0}`) wording does not control the


variable [NormedAddCommGroup E] [NormedSpace ℂ E]
/--
[integrableOn_mul_exp_neg_Ioi'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/ExponentialBound.lean)
-/
@[path]
private lemma integrableOn_mul_exp_neg_Ioi' {r : ℝ} (hr : 0 < r) :
  IntegrableOn (fun t : ℝ => t * Real.exp (-r * t))
    (Set.Ioi (0 : ℝ)) := by
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  apply integrable_of_isBigO_exp_neg hr2
  · exact (continuous_id.mul
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id'))).continuousOn
  · rw [Asymptotics.isBigO_iff]
    use 2 / r
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht (Real.exp_nonneg _))]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hle : t ≤ (2 / r) * Real.exp (r / 2 * t) :=
      calc t = (2 / r) * (r / 2 * t) := by field_simp
        _ ≤ (2 / r) * Real.exp (r / 2 * t) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [Real.add_one_le_exp (r / 2 * t)]
    calc t * Real.exp (-r * t)
      = t * (Real.exp (-(r / 2) * t) *
        Real.exp (-(r / 2) * t)) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      _ ≤ (2 / r) * Real.exp (r / 2 * t) *
        (Real.exp (-(r / 2) * t) *
          Real.exp (-(r / 2) * t)) := by
        apply mul_le_mul_of_nonneg_right hle
        exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = (2 / r) * (Real.exp (r / 2 * t) *
        Real.exp (-(r / 2) * t)) *
        Real.exp (-(r / 2) * t) := by ring
      _ = 2 / r * Real.exp (-(r / 2) * t) := by
        rw [← Real.exp_add]
        simp only [neg_mul, add_neg_cancel, Real.exp_zero]
        ring

/--
[laplaceConvergent_of_norm_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/ExponentialBound.lean)
-/
@[path]
lemma laplaceConvergent_of_norm_le_exp
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {a C : ℝ}
  {s : ℂ}
-- given
  (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
  (hC : 0 ≤ C)
  (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t))
  (hs : a < s.re) :
-- imply
  LaplaceConvergent f s := by
-- proof
  unfold LaplaceConvergent
  have hpos : 0 < s.re - a := sub_pos.mpr hs
  have hbound_int :
    IntegrableOn (fun t : ℝ => C * Real.exp (-(s.re - a) * t))
      (Set.Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 hpos).const_mul C
  have hexp : AEStronglyMeasurable
    (fun t : ℝ => Complex.exp (-s * (t : ℂ)))
    (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
    (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t)
    (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hexp.smul hf
  apply Integrable.mono hbound_int hmeas
  rw [ae_restrict_iff' measurableSet_Ioi]
  apply ae_of_all
  intro t ht
  simp only [Set.mem_Ioi] at ht
  rw [norm_smul, Complex.norm_exp]
  have hre : (-s * (t : ℂ)).re = -s.re * t := by
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
  rw [hre]
  calc Real.exp (-s.re * t) * ‖f t‖
    ≤ Real.exp (-s.re * t) * (C * Real.exp (a * t)) :=
      mul_le_mul_of_nonneg_left (hbound t (le_of_lt ht))
        (Real.exp_nonneg _)
    _ = C * Real.exp (-(s.re - a) * t) := by
      rw [show -(s.re - a) * t = -s.re * t + a * t from by ring]
      rw [Real.exp_add]
      ring
    _ ≤ ‖C * Real.exp (-(s.re - a) * t)‖ := by
      rw [Real.norm_of_nonneg
        (mul_nonneg hC (Real.exp_nonneg _))]

/--
[laplaceConvergent_of_isBigO_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/ExponentialBound.lean)
-/
@[path]
lemma laplaceConvergent_of_isBigO_exp
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {a : ℝ}
  {s : ℂ}
-- given
  (hloc : LocallyIntegrableOn f (Set.Ici 0))
  (ho : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t)))
  (hs : a < s.re) :
-- imply
  LaplaceConvergent f s := by
-- proof
  unfold LaplaceConvergent
  set r : ℝ := s.re - a with hr_def
  have hr : 0 < r := sub_pos.mpr hs
  have hcont_exp : Continuous (fun t : ℝ => Complex.exp (-s * (t : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hF_loc : LocallyIntegrableOn
    (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t) (Set.Ici 0) :=
    hloc.continuousOn_smul isClosed_Ici.isLocallyClosed hcont_exp.continuousOn
  have hg_ioi : IntegrableOn (fun t : ℝ => Real.exp (-r * t))
    (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 hr
  have htail : IntegrableAtFilter (fun t : ℝ => Real.exp (-r * t))
    Filter.atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp hg_ioi).1
  have hbig : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t)
    =O[Filter.atTop] (fun t : ℝ => Real.exp (-r * t)) := by
    rw [Asymptotics.isBigO_iff] at ho ⊢
    obtain ⟨C, hC⟩ := ho
    refine ⟨C, ?_⟩
    filter_upwards [hC] with t ht
    rw [norm_smul, Complex.norm_exp]
    have hre : (-s * (t : ℂ)).re = -s.re * t := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-s.re * t) * ‖f t‖
      ≤ Real.exp (-s.re * t) * (C * Real.exp (a * t)) :=
        mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
      _ = C * Real.exp (-r * t) := by
        rw [hr_def, show -((s.re - a)) * t = -s.re * t + a * t from by ring]
        rw [Real.exp_add]
        ring
  have hIci : IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t)
    (Set.Ici (0 : ℝ)) :=
    hF_loc.integrableOn_of_isBigO_atTop hbig htail
  exact hIci.mono_set Set.Ioi_subset_Ici_self

/--
[differentiableOn_laplace_of_norm_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/ExponentialBound.lean)
-/
@[path]
lemma differentiableOn_laplace_of_norm_le_exp
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℝ → E}
  {a C : ℝ}
-- given
  (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
  (hC : 0 ≤ C)
  (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t)) :
-- imply
  DifferentiableOn ℂ (laplace f) {s | a < s.re} := by
-- proof
  intro s₀ hs₀
  simp only [Set.mem_ofPred_eq] at hs₀
  set μ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ_def
  set δ := (s₀.re - a) / 2 with hδ_def
  set b := (s₀.re + a) / 2 with hb_def
  have hδ : 0 < δ := by
    simp only [hδ_def]
    linarith
  have hba : 0 < b - a := by
    simp only [hb_def]
    linarith
  have hball_re : ∀ z ∈ Metric.ball s₀ δ, b ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have habs_re : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
      rw [← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have hlt : |z.re - s₀.re| < δ := lt_of_le_of_lt habs_re hz
    have hmem := abs_lt.mp hlt
    simp only [hb_def, hδ_def] at hmem ⊢
    linarith [hmem.1, hmem.2]
  have hmeas_F : ∀ z : ℂ, AEStronglyMeasurable
    (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t) μ := by
    intro z
    have hexp : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply Continuous.aestronglyMeasurable
      exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hexp.smul hf
  have hF_int : Integrable
    (fun t : ℝ => Complex.exp (-s₀ * (t : ℂ)) • f t) μ := by
    have hconv := laplaceConvergent_of_norm_le_exp f a C hf hC hbound
      (show a < s₀.re from hs₀)
    unfold LaplaceConvergent at hconv
    rwa [hμ_def]
  have hmeas_deriv : AEStronglyMeasurable
    (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) • f t)
    μ := by
    have hcont : Continuous
      (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) :
        ℝ → ℂ) := by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.neg
      · exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hcont.aestronglyMeasurable.smul hf
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (-s * (t : ℂ)) • f t)
    (F' := fun (s : ℂ) (t : ℝ) =>
      (-(t : ℂ) * Complex.exp (-s * (t : ℂ))) • f t)
    (bound := fun t : ℝ => C * |t| * Real.exp (-(b - a) * t))
    (s := Metric.ball s₀ δ)
    (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ hδ)
    (Filter.Eventually.of_forall (fun z => hmeas_F z))
    hF_int
    hmeas_deriv
    ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply ae_of_all
    intro t ht z hz
    simp only [Set.mem_Ioi] at ht
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = -z.re * t := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    have hht : ‖f t‖ ≤ C * Real.exp (a * t) := hbound t (le_of_lt ht)
    have hb : b ≤ z.re := hball_re z hz
    calc |t| * Real.exp (-z.re * t) * ‖f t‖
      ≤ |t| * Real.exp (-b * t) * ‖f t‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp_of_le
            (mul_le_mul_of_nonneg_right (neg_le_neg hb)
              (le_of_lt ht)))
          (abs_nonneg t)
      _ ≤ |t| * Real.exp (-b * t) * (C * Real.exp (a * t)) := by
        apply mul_le_mul_of_nonneg_left hht
        exact mul_nonneg (abs_nonneg t) (Real.exp_nonneg _)
      _ = C * |t| * Real.exp (-(b - a) * t) := by
        rw [show -(b - a) * t = -b * t + a * t from by ring]
        rw [Real.exp_add]
        ring
  · rw [hμ_def]
    change IntegrableOn
      (fun t : ℝ => C * |t| * Real.exp (-(b - a) * t))
      (Set.Ioi (0 : ℝ))
    have h1 : IntegrableOn
      (fun t : ℝ => C * (t * Real.exp (-(b - a) * t)))
      (Set.Ioi (0 : ℝ)) :=
      (integrableOn_mul_exp_neg_Ioi' hba).const_mul C
    apply h1.congr_fun _ measurableSet_Ioi
    intro t ht
    simp only [Set.mem_Ioi] at ht
    change C * (t * Real.exp (-(b - a) * t)) =
      C * |t| * Real.exp (-(b - a) * t)
    rw [abs_of_pos ht]
    ring
  · apply ae_of_all
    intro t z _
    have h1 : HasDerivAt (fun s : ℂ => -s * (t : ℂ)) (-(t : ℂ)) z := by
      have hder := (hasDerivAt_neg (𝕜 := ℂ) z).mul_const (t : ℂ)
      simp only [neg_one_mul] at hder
      exact hder
    have h2 := h1.cexp.smul_const (f t)
    have heq : Complex.exp (-z * (t : ℂ)) * (-(t : ℂ)) =
      -(t : ℂ) * Complex.exp (-z * (t : ℂ)) := mul_comm _ _
    rwa [heq] at h2

/--
[differentiableOn_laplace_of_isBigO_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/ExponentialBound.lean)
-/
@[path]
lemma differentiableOn_laplace_of_isBigO_exp
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℝ → E}
  {a : ℝ}
-- given
  (hf : LocallyIntegrableOn f (Set.Ici 0))
  (hO : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t))) :
-- imply
  DifferentiableOn ℂ (laplace f) {s | a < s.re} := by
-- proof
  intro s₀ hs₀
  simp only [Set.mem_ofPred_eq] at hs₀
  set μ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ_def
  set δ := (s₀.re - a) / 2 with hδ_def
  set b := (s₀.re + a) / 2 with hb_def
  have hδ : 0 < δ := by
    simp only [hδ_def]
    linarith
  have hab : a < b := by
    simp only [hb_def]
    linarith
  have hba : 0 < b - a := sub_pos.mpr hab
  have hball_re : ∀ z ∈ Metric.ball s₀ δ, b ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have habs_re : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
      rw [← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have hlt : |z.re - s₀.re| < δ := lt_of_le_of_lt habs_re hz
    have hmem := abs_lt.mp hlt
    simp only [hb_def, hδ_def] at hmem ⊢
    linarith [hmem.1, hmem.2]
  have hfIoi : LocallyIntegrableOn f (Set.Ioi (0 : ℝ)) :=
    hf.mono_set Set.Ioi_subset_Ici_self
  have hmeas_F : ∀ z : ℂ, AEStronglyMeasurable
    (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t) μ := by
    intro z
    have hexp : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply Continuous.aestronglyMeasurable
      exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hexp.smul hfIoi.aestronglyMeasurable
  have hF_int : Integrable
    (fun t : ℝ => Complex.exp (-s₀ * (t : ℂ)) • f t) μ := by
    have hconv := laplaceConvergent_of_isBigO_exp f a hf hO
      (show a < s₀.re from hs₀)
    unfold LaplaceConvergent at hconv
    rwa [hμ_def]
  have hmeas_deriv : AEStronglyMeasurable
    (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) • f t)
    μ := by
    have hcont : Continuous
      (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) :
        ℝ → ℂ) := by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.neg
      · exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hcont.aestronglyMeasurable.smul hfIoi.aestronglyMeasurable
  have hB_loc : LocallyIntegrableOn
    (fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖) (Set.Ici 0) := by
    have hcont : ContinuousOn (fun t : ℝ => |t| * Real.exp (-b * t))
      (Set.Ici (0 : ℝ)) :=
      (continuous_abs.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id'))).continuousOn
    exact hf.norm.continuousOn_mul hcont isClosed_Ici.isLocallyClosed
  have hcomp_int : IntegrableAtFilter
    (fun t : ℝ => t * Real.exp (-(b - a) * t)) Filter.atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp
      (integrableOn_mul_exp_neg_Ioi' hba)).1
  have hbig : (fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖)
    =O[Filter.atTop]
    (fun t : ℝ => t * Real.exp (-(b - a) * t)) := by
    rw [Asymptotics.isBigO_iff] at hO ⊢
    obtain ⟨C, hC⟩ := hO
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_ge_atTop (0 : ℝ)] with t ht ht0
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at ht
    show ‖|t| * Real.exp (-b * t) * ‖f t‖‖ ≤
      C * ‖t * Real.exp (-(b - a) * t)‖
    have hnn : 0 ≤ |t| * Real.exp (-b * t) * ‖f t‖ :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
        (norm_nonneg _)
    have hnn2 : 0 ≤ t * Real.exp (-(b - a) * t) :=
      mul_nonneg ht0 (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn,
      Real.norm_eq_abs, abs_of_nonneg hnn2, abs_of_nonneg ht0]
    calc t * Real.exp (-b * t) * ‖f t‖
      ≤ t * Real.exp (-b * t) * (C * Real.exp (a * t)) :=
        mul_le_mul_of_nonneg_left ht
          (mul_nonneg ht0 (Real.exp_nonneg _))
      _ = C * (t * Real.exp (-(b - a) * t)) := by
        rw [show -(b - a) * t = -b * t + a * t from by ring]
        rw [Real.exp_add]
        ring
  have hbound_int : Integrable
    (fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖) μ := by
    rw [hμ_def]
    exact (hB_loc.integrableOn_of_isBigO_atTop hbig hcomp_int).mono_set
      Set.Ioi_subset_Ici_self
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (-s * (t : ℂ)) • f t)
    (F' := fun (s : ℂ) (t : ℝ) =>
      (-(t : ℂ) * Complex.exp (-s * (t : ℂ))) • f t)
    (bound := fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖)
    (s := Metric.ball s₀ δ)
    (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ hδ)
    (Filter.Eventually.of_forall (fun z => hmeas_F z))
    hF_int
    hmeas_deriv
    ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply ae_of_all
    intro t ht z hz
    simp only [Set.mem_Ioi] at ht
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = -z.re * t := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    have hb : b ≤ z.re := hball_re z hz
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp_of_le
          (mul_le_mul_of_nonneg_right (neg_le_neg hb) (le_of_lt ht)))
        (abs_nonneg t))
      (norm_nonneg _)
  · exact hbound_int
  · apply ae_of_all
    intro t z _
    have h1 : HasDerivAt (fun s : ℂ => -s * (t : ℂ)) (-(t : ℂ)) z := by
      have hder := (hasDerivAt_neg (𝕜 := ℂ) z).mul_const (t : ℂ)
      simp only [neg_one_mul] at hder
      exact hder
    have h2 := h1.cexp.smul_const (f t)
    have heq : Complex.exp (-z * (t : ℂ)) * (-(t : ℂ)) =
      -(t : ℂ) * Complex.exp (-z * (t : ℂ)) := mul_comm _ _
    rwa [heq] at h2


-- created on 2026-10-20
-- updated on 2026-10-26
