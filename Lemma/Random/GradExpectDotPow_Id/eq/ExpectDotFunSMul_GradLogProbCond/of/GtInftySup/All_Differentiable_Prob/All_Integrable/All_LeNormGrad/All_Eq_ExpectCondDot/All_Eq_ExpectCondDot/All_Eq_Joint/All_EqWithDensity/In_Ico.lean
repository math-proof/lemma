import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Theorem.Function
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.ExpectDotPow_Id.eq.Integral_ExtDotPow_Id.of.All_EqWithDensity
import Lemma.Random.GetTSum_SMul.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral_Fderiv_Vkd.eq.TSum_SMul_Integral_SMul_Qkd_FderivLog.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Kf.eq.Integral.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.MeasurableRkd
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.TSum_SMul.eq.Integral_Fderiv_Vkd.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Theorem.Probability.JointRv.AsRV
open Classical MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Finset Kernel
set_option maxHeartbeats 900000


private lemma avg_Kf_clip
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (j : ℕ)
  (x : 𝒮) :
-- imply
  ∫ z, M.Kf θ (fun w : (ℝ × 𝒮 × 𝒜) ↦ clip w.1 (-M.env.R) M.env.R) j z ∂(M.stageK θ x) =
    M.Wkd θ j x := by
-- proof
  have := M.env.reward_markov
  have := M.env.trans_markov
  let clipf : (ℝ × 𝒮 × 𝒜) → ℝ := fun w ↦ clip w.1 (-M.env.R) M.env.R
  have hf : StronglyMeasurable clipf := by
    unfold clipf clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ w : (ℝ × 𝒮 × 𝒜), ‖clipf w‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  induction j generalizing x with
  | zero =>
    have e :=
      Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ x
    simpa [clipf, DensityModel.Kf, DensityModel.Wkd, DensityModel.rkd, smul_eq_mul] using e
  | succ j ih =>
    have hKf :=
      StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ j
    have hπ : ∀ θ', Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ' z.1 z.2) :=
      fun θ' => M.policy.measurable_prob θ'
    have hmeas : Measurable (M.Wkd θ j) :=
      Measurable_Wkd.of.All_Measurable_Prob (M := M) hπ θ j
    have hφ : StronglyMeasurable (fun p : 𝒮 × 𝒜 => ∫ y, M.Wkd θ j y ∂(M.env.trans p)) :=
      (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
        (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.Wkd θ j z.2)
        (hmeas.stronglyMeasurable.comp_measurable measurable_snd)).measurable.stronglyMeasurable
    have hfw : StronglyMeasurable (fun z : (ℝ × 𝒮 × 𝒜) => ∫ y, M.Wkd θ j y ∂(M.env.trans z.2)) :=
      hφ.comp_measurable measurable_snd
    have hCw : ∀ z : ℝ × 𝒮 × 𝒜, ‖∫ y, M.Wkd θ j y ∂(M.env.trans z.2)‖ ≤ |M.env.R| := by
      intro z
      simpa using norm_integral_le_of_norm_le_const (μ := M.env.trans z.2)
        (Filter.Eventually.of_forall fun y => NormWkd.le.Abs_R (M := M) θ j y)
    have hpt : ∀ z, M.Kf θ clipf (j + 1) z = ∫ y, M.Wkd θ j y ∂(M.env.trans z.2) := by
      intro z
      rw [Kf.eq.Integral.All_EqWithDensity (M := M) (f := clipf) θ j z]
      have hInt : Integrable (M.Kf θ clipf j) ((M.env.trans z.2).bind (M.stageK θ)) :=
        Integrable.of_bound hKf.1.aestronglyMeasurable |M.env.R| (Filter.Eventually.of_forall hKf.2)
      have hbind : M.K θ z = (M.env.trans z.2).bind (M.stageK θ) := by
        rw [DensityModel.K, Kernel.comp_apply, Kernel.comap_apply]
      rw [hbind, Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      exact ih y
    have hfun : (fun z : (ℝ × 𝒮 × 𝒜) =>
        M.Kf θ (fun w : (ℝ × 𝒮 × 𝒜) => clip w.1 (-M.env.R) M.env.R) (j + 1) z) =
        fun z => ∫ y, M.Wkd θ j y ∂(M.env.trans z.2) := by
      funext z
      exact hpt z
    rw [hfun]
    refine (Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hfw hCw θ x).trans ?_
    simp only [DensityModel.Wkd, smul_eq_mul]
    congr 1
    funext u
    have : IsProbabilityMeasure (M.env.reward (x, u)) := inferInstance
    rw [MeasureTheory.integral_const, probReal_univ, one_smul]

private lemma Kf_succ_eq_Wkd
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (j : ℕ)
  (z : ℝ × 𝒮 × 𝒜) :
-- imply
  M.Kf θ (fun w : (ℝ × 𝒮 × 𝒜) ↦ clip w.1 (-M.env.R) M.env.R) (j + 1) z =
    ∫ y, M.Wkd θ j y ∂(M.env.trans z.2) := by
-- proof
  have := M.env.reward_markov
  have := M.env.trans_markov
  let clipf : (ℝ × 𝒮 × 𝒜) → ℝ := fun w ↦ clip w.1 (-M.env.R) M.env.R
  have hf : StronglyMeasurable clipf := by
    unfold clipf clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ w : (ℝ × 𝒮 × 𝒜), ‖clipf w‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  have hKf :=
    StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ j
  rw [Kf.eq.Integral.All_EqWithDensity (M := M) (f := clipf) θ j z]
  have hInt : Integrable (M.Kf θ clipf j) ((M.env.trans z.2).bind (M.stageK θ)) :=
    Integrable.of_bound hKf.1.aestronglyMeasurable |M.env.R| (Filter.Eventually.of_forall hKf.2)
  have hbind : M.K θ z = (M.env.trans z.2).bind (M.stageK θ) := by
    rw [DensityModel.K, Kernel.comp_apply, Kernel.comap_apply]
  rw [hbind, Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact avg_Kf_clip (M := M) θ j y

private lemma integral_comp_stageK
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {f : (ℝ × 𝒮 × 𝒜) → E}
  {C : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, f (ω t) ∂(M θ) =
    ∫ y, (∫ z, f z ∂(M.stageK θ y)) ∂((M θ).map (s t)) := by
-- proof
  have ht : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => ω t) := measurable_pi_apply t
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₀ t
  have := M.env.init_prob
  have : IsProbabilityMeasure (M θ) := inferInstance
  have : IsProbabilityMeasure ((M θ).map (s t)) := inferInstance
  rw [← integral_map (μ := M θ) ht.aemeasurable hf.aestronglyMeasurable,
      Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₀ θ t,
      Integral.eq.Integral_Integral.of.Integrable_Bind
        (Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC))]

/--
The path-discounted return starting at time `t`, integrated against a bounded score of
`(s t, a t)`, agrees with the Bellman action value `rkd + γ ∫ V0 ∂trans`.
-/
private lemma integral_mul_return_eq_Qf
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {c : 𝒮 → 𝒜 → ℝ}
  {Cc : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hc : StronglyMeasurable (Function.uncurry c))
  (hCc : ∀ y u, ‖c y u‖ ≤ Cc)
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω * c (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, (M.rkd (s t ω) (a t ω) +
        γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (s t ω, a t ω))) *
      c (s t ω) (a t ω) ∂(M θ) := by
-- proof
  have := M.env.reward_markov
  have := M.env.trans_markov
  have := M.env.init_prob
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₁ t
  have ha : Measurable (a t) := Random.Measurable.of.All_Eq.snd.snd h₁ t
  have hr : ∀ k, Measurable (r k) := fun k => Random.Measurable.of.All_Eq.fst h₁ k
  let clipf : (ℝ × 𝒮 × 𝒜) → ℝ := fun w ↦ clip w.1 (-M.env.R) M.env.R
  have hf : StronglyMeasurable clipf := by
    unfold clipf clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hclipC : ∀ w, ‖clipf w‖ ≤ |M.env.R| := fun w => NormClip.le.Abs_R M.env.R w.1
  set Cc' : ℝ := max Cc 0
  have hCc' : 0 ≤ Cc' := le_max_right _ _
  have hCcle : ∀ y u, ‖c y u‖ ≤ Cc' := fun y u => (hCc y u).trans (le_max_left _ _)
  set BG : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBG : 0 ≤ BG :=
    mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hGeq : ∀ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω = ∑' k, γ ^ k * r (t + k) ω := by
    intro ω
    simp [Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
  have hrbd : ∀ k, ∀ᵐ ω ∂(M θ), ‖r k ω‖ ≤ |M.env.R| := fun k =>
    (All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ).mono fun ω h => h k
  have hprod_int : ∀ k, Integrable
    (fun ω => r (t + k) ω * c (s t ω) (a t ω)) (M θ) := fun k =>
    Integrable.of_bound
      ((hr (t + k)).stronglyMeasurable.mul
        (hc.comp_measurable (hs.prodMk ha))).aestronglyMeasurable
      (|M.env.R| * Cc')
      (Filter.Eventually.mono (hrbd (t + k)) fun ω hω => by
        rw [norm_mul]
        exact mul_le_mul hω (hCcle _ _) (norm_nonneg _) (abs_nonneg _))
  have hGbd : ∀ᵐ ω ∂(M θ), ‖∑' k, γ ^ k * r (t + k) ω‖ ≤ BG := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hrω
    have hsum : Summable fun k => γ ^ k * |M.env.R| :=
      (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    have hle : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hrω (t + k))
        (pow_nonneg h₀.1 k)
    have hsn : Summable fun k => ‖γ ^ k * r (t + k) ω‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
    calc
      _ ≤ ∑' k, ‖γ ^ k * r (t + k) ω‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, γ ^ k * |M.env.R| := Summable.tsum_le_tsum hle hsn hsum
      _ = BG := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
  have hswap :
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω * c (s t ω) (a t ω) ∂(M θ) =
      ∑' k, γ ^ k * ∫ ω, r (t + k) ω * c (s t ω) (a t ω) ∂(M θ) := by
    have hterm : ∀ k, Integrable
      (fun ω => γ ^ k * (r (t + k) ω * c (s t ω) (a t ω))) (M θ) := fun k =>
      (hprod_int k).const_mul (γ ^ k)
    have hSn : Summable (fun k => ∫ ω,
        ‖γ ^ k * (r (t + k) ω * c (s t ω) (a t ω))‖ ∂(M θ)) := by
      refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun k => ?_) ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (|M.env.R| * Cc'))
      have hbd : ∀ᵐ ω ∂(M θ),
          ‖γ ^ k * (r (t + k) ω * c (s t ω) (a t ω))‖ ≤ γ ^ k * (|M.env.R| * Cc') := by
        filter_upwards [hrbd (t + k)] with ω hω
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 k)
        exact mul_le_mul hω (hCcle _ _) (norm_nonneg _) (abs_nonneg _)
      calc
        _ ≤ ∫ _, γ ^ k * (|M.env.R| * Cc') ∂(M θ) :=
          integral_mono_ae (hterm k).norm (integrable_const _) hbd
        _ = γ ^ k * (|M.env.R| * Cc') := by
          rw [MeasureTheory.integral_const]
          simp [probReal_univ, smul_eq_mul]
    have hfun : (fun ω => ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω * c (s t ω) (a t ω)) =
        fun ω => ∑' k, γ ^ k * (r (t + k) ω * c (s t ω) (a t ω)) := by
      funext ω
      rw [hGeq, ← tsum_mul_right]
      exact tsum_congr fun k => mul_assoc _ _ _
    rw [hfun, ← integral_tsum_of_summable_integral_norm hterm hSn]
    exact tsum_congr fun k => integral_const_mul _ _
  rw [hswap]
  have h0 :
    ∫ ω, r t ω * c (s t ω) (a t ω) ∂(M θ) =
      ∫ ω, M.rkd (s t ω) (a t ω) * c (s t ω) (a t ω) ∂(M θ) := by
    have hsa : ∀ ω, (s t ω, a t ω) = ((ω t).2.1, (ω t).2.2) := fun ω => by
      have h := congrFun (h₁ t) ω
      exact (Prod.ext (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2) h)).symm
    have hL : (fun ω => r t ω * c (s t ω) (a t ω)) =ᵐ[M θ]
        fun ω => clipf (ω t) * c (s t ω) (a t ω) := by
      filter_upwards [MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₁ θ t] with ω hω
      rw [hω]
    rw [integral_congr_ae hL]
    let f : (ℝ × 𝒮 × 𝒜) → ℝ := fun z => clipf z * c z.2.1 z.2.2
    have hf' : StronglyMeasurable f :=
      hf.mul (hc.comp_measurable (measurable_snd.fst.prodMk measurable_snd.snd))
    have hCf : ∀ z, ‖f z‖ ≤ |M.env.R| * Cc' := fun z => by
      rw [norm_mul]
      exact mul_le_mul (hclipC z) (hCcle _ _) (norm_nonneg _) (abs_nonneg _)
    have hfunf : (fun ω => clipf (ω t) * c (s t ω) (a t ω)) = fun ω => f (ω t) := by
      funext ω
      simp only [f]
      congr 1
      exact congrArg (fun p : 𝒮 × 𝒜 => c p.1 p.2) (hsa ω)
    rw [hfunf, integral_comp_stageK (M := M) h₁ hf' hCf θ t]
    have hinter : ∀ y,
        ∫ z, f z ∂(M.stageK θ y) =
          ∫ u, M.policy.prob θ y u • (M.rkd y u * c y u) ∂ReferenceMeasure.measure := by
      intro y
      have e :=
        Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hf' hCf θ y
      refine e.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
      have hinner : ∫ ρ, clipf (ρ, y, u) * c y u ∂(M.env.reward (y, u)) =
          M.rkd y u * c y u := by
        have hcst : ∫ ρ, clipf (ρ, y, u) * c y u ∂(M.env.reward (y, u)) =
            (∫ ρ, clipf (ρ, y, u) ∂(M.env.reward (y, u))) * c y u := by
          simpa [mul_comm] using
            (integral_mul_const (μ := M.env.reward (y, u)) (r := c y u)
              (f := fun ρ => clipf (ρ, y, u)))
        have hrkd : ∫ ρ, clipf (ρ, y, u) ∂(M.env.reward (y, u)) = M.rkd y u := by
          simp [clipf, DensityModel.rkd]
        rw [hcst, hrkd]
      simpa [f, smul_eq_mul] using congrArg (fun z => M.policy.prob θ y u * z) hinner
    simp_rw [hinter]
    refine (Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
      (M := M) (φ := fun y u => M.rkd y u * c y u)
      (C := |M.env.R| * Cc') h₁
      (MeasurableRkd (M := M).stronglyMeasurable.mul hc)
      (fun y u => by
        rw [norm_mul]
        exact mul_le_mul (NormRkd.le.Abs_R (M := M) y u) (hCcle y u)
          (norm_nonneg _) (abs_nonneg _))
      θ t).symm
  have hsucc : ∀ j,
      ∫ ω, r (t + (j + 1)) ω * c (s t ω) (a t ω) ∂(M θ) =
        ∫ ω, c (s t ω) (a t ω) *
          (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω))) ∂(M θ) := by
    intro j
    have hL : (fun ω => r (t + (j + 1)) ω * c (s t ω) (a t ω)) =ᵐ[M θ]
        fun ω => clipf (ω (t + (j + 1))) * c (s t ω) (a t ω) := by
      filter_upwards [MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₁ θ (t + (j + 1))] with ω hω
      rw [hω]
    rw [integral_congr_ae hL]
    let G : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → ℝ :=
      fun hist => c (hist (⟨t, mem_Iic.2 le_rfl⟩ : Finset.Iic t)).2.1 (hist (⟨t, mem_Iic.2 le_rfl⟩ : Finset.Iic t)).2.2
    have hG : StronglyMeasurable G :=
      hc.comp_measurable
        ((measurable_snd.fst.comp (measurable_pi_apply (⟨t, mem_Iic.2 le_rfl⟩ : Finset.Iic t))).prodMk
          (measurable_snd.snd.comp (measurable_pi_apply (⟨t, mem_Iic.2 le_rfl⟩ : Finset.Iic t))))
    have hCG : ∀ hist, ‖G hist‖ ≤ Cc' := fun hist => hCcle _ _
    have hGapp : ∀ ω : ℕ → ℝ × 𝒮 × 𝒜,
        G (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω) =
          c (s t ω) (a t ω) := by
      intro ω
      have h := congrFun (h₁ t) ω
      simp only [G, Preorder.frestrictLe_apply]
      have hs : (ω t).2.1 = s t ω := congrArg (fun z => z.2.1) h
      have ha : (ω t).2.2 = a t ω := congrArg (fun z => z.2.2) h
      rw [hs, ha]
    have hmark :=
      All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hclipC θ (j + 1) t hG hCG
    have hfun : (fun ω => clipf (ω (t + (j + 1))) * c (s t ω) (a t ω)) =
        fun ω => G (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω) *
          clipf (ω (t + (j + 1))) := by
      funext ω
      rw [hGapp, mul_comm]
    rw [hfun, hmark]
    have hfun' : (fun ω =>
        G (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω) *
          M.Kf θ clipf (j + 1) (ω t)) =
        fun ω => c (s t ω) (a t ω) *
          (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω))) := by
      funext ω
      have hsa : (ω t).2 = (s t ω, a t ω) := by
        have h := congrFun (h₁ t) ω
        exact Prod.ext (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2) h)
      rw [hGapp, Kf_succ_eq_Wkd (M := M) θ j (ω t), hsa]
    rw [hfun']
  have htail :
    ∑' j, γ ^ (j + 1) * ∫ ω, r (t + (j + 1)) ω * c (s t ω) (a t ω) ∂(M θ) =
      ∫ ω, (γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (s t ω, a t ω))) *
        c (s t ω) (a t ω) ∂(M θ) := by
    have hrew : ∀ j,
        γ ^ (j + 1) * ∫ ω, r (t + (j + 1)) ω * c (s t ω) (a t ω) ∂(M θ) =
          γ ^ (j + 1) * ∫ ω, c (s t ω) (a t ω) *
            (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω))) ∂(M θ) :=
      fun j => congrArg (fun z => γ ^ (j + 1) * z) (hsucc j)
    simp_rw [hrew]
    have hπ : ∀ θ', Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ' z.1 z.2) :=
      fun θ' => M.policy.measurable_prob θ'
    have hV0m : Measurable (M.V0 θ γ) :=
      Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ
    have hW : ∀ j, Measurable (M.Wkd θ j) := fun j =>
      Measurable_Wkd.of.All_Measurable_Prob (M := M) hπ θ j
    have hinterW : ∀ j, StronglyMeasurable
      (fun p : 𝒮 × 𝒜 => ∫ y, M.Wkd θ j y ∂(M.env.trans p)) := fun j =>
      (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
        (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.Wkd θ j z.2)
        ((hW j).stronglyMeasurable.comp_measurable measurable_snd)).measurable.stronglyMeasurable
    have htermW : ∀ j, Integrable
      (fun ω => c (s t ω) (a t ω) *
          (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω)))) (M θ) := fun j =>
      Integrable.of_bound
        ((hc.comp_measurable (hs.prodMk ha)).mul
          ((hinterW j).comp_measurable (hs.prodMk ha))).aestronglyMeasurable
        (Cc' * |M.env.R|)
        (Filter.Eventually.of_forall fun ω => by
          rw [norm_mul]
          refine mul_le_mul (hCcle _ _) ?_ (norm_nonneg _) hCc'
          have : IsProbabilityMeasure (M.env.trans (s t ω, a t ω)) := inferInstance
          simpa [probReal_univ] using
            (norm_integral_le_of_norm_le_const
              (μ := M.env.trans (s t ω, a t ω))
              (Filter.Eventually.of_forall fun y => NormWkd.le.Abs_R (M := M) θ j y)))
    have hgeo : Summable (fun j => γ ^ (j + 1) * (Cc' * |M.env.R|)) := by
      simp_rw [pow_succ]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (Cc' * |M.env.R|)).mul_left γ
    have hSnW : Summable (fun j => ∫ ω, ‖γ ^ (j + 1) * (c (s t ω) (a t ω) *
          (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω))))‖ ∂(M θ)) := by
      refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun j => ?_) hgeo
      have hbd : ∀ᵐ ω ∂(M θ),
          ‖γ ^ (j + 1) * (c (s t ω) (a t ω) *
            (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω))))‖ ≤
            γ ^ (j + 1) * (Cc' * |M.env.R|) :=
        Filter.Eventually.of_forall fun ω => by
          rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 (j + 1))
          refine mul_le_mul (hCcle _ _) ?_ (norm_nonneg _) hCc'
          have : IsProbabilityMeasure (M.env.trans (s t ω, a t ω)) := inferInstance
          simpa [probReal_univ] using
            (norm_integral_le_of_norm_le_const
              (μ := M.env.trans (s t ω, a t ω))
              (Filter.Eventually.of_forall fun y => NormWkd.le.Abs_R (M := M) θ j y))
      have hterm : Integrable
        (fun ω => γ ^ (j + 1) * (c (s t ω) (a t ω) *
            (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω))))) (M θ) :=
        (htermW j).const_mul (γ ^ (j + 1))
      calc
        _ ≤ ∫ _, γ ^ (j + 1) * (Cc' * |M.env.R|) ∂(M θ) :=
          integral_mono_ae hterm.norm (integrable_const _) hbd
        _ = γ ^ (j + 1) * (Cc' * |M.env.R|) := by
          rw [MeasureTheory.integral_const]
          simp [probReal_univ, smul_eq_mul]
    have htermγ : ∀ j, Integrable
      (fun ω => γ ^ (j + 1) * (c (s t ω) (a t ω) *
          (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω))))) (M θ) :=
      fun j => (htermW j).const_mul (γ ^ (j + 1))
    have hpull : ∀ j,
        γ ^ (j + 1) * ∫ ω, c (s t ω) (a t ω) *
            (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω))) ∂(M θ) =
          ∫ ω, γ ^ (j + 1) * (c (s t ω) (a t ω) *
            (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω)))) ∂(M θ) :=
      fun j => (integral_const_mul (γ ^ (j + 1)) _).symm
    simp_rw [hpull]
    refine (integral_tsum_of_summable_integral_norm htermγ hSnW).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hts :
      ∑' j, γ ^ (j + 1) * (c (s t ω) (a t ω) *
            (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω)))) =
          (γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (s t ω, a t ω))) * c (s t ω) (a t ω) := by
      have hfact : ∀ j,
          γ ^ (j + 1) * (c (s t ω) (a t ω) *
            (∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω)))) =
            (γ * (γ ^ j * ∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω)))) *
              c (s t ω) (a t ω) := by
        intro j
        rw [pow_succ]
        ring
      simp_rw [hfact]
      rw [tsum_mul_right, tsum_mul_left]
      have hinter :
        ∑' j, γ ^ j * ∫ y, M.Wkd θ j y ∂(M.env.trans (s t ω, a t ω)) =
            ∫ y, M.V0 θ γ y ∂(M.env.trans (s t ω, a t ω)) := by
        have hri : ∀ j, Integrable (fun y => γ ^ j * M.Wkd θ j y)
            (M.env.trans (s t ω, a t ω)) := fun j =>
          Integrable.of_bound ((hW j).const_mul (γ ^ j)).aestronglyMeasurable
            (γ ^ j * |M.env.R|)
            (Filter.Eventually.of_forall fun y => by
              rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
              exact mul_le_mul_of_nonneg_left (NormWkd.le.Abs_R (M := M) θ j y)
                (pow_nonneg h₀.1 j))
        have hSn : Summable (fun j => ∫ y, ‖γ ^ j * M.Wkd θ j y‖
            ∂(M.env.trans (s t ω, a t ω))) := by
          refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
            (fun j => ?_) ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
          calc
            _ ≤ ∫ _, γ ^ j * |M.env.R| ∂(M.env.trans (s t ω, a t ω)) :=
              integral_mono_ae (hri j).norm (integrable_const _)
                (Filter.Eventually.of_forall fun y => by
                  change ‖γ ^ j * M.Wkd θ j y‖ ≤ γ ^ j * |M.env.R|
                  rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
                  exact mul_le_mul_of_nonneg_left (NormWkd.le.Abs_R (M := M) θ j y)
                    (pow_nonneg h₀.1 j))
            _ = γ ^ j * |M.env.R| := by
              simp [MeasureTheory.integral_const, probReal_univ]
        simp_rw [← integral_const_mul, DensityModel.V0]
        exact integral_tsum_of_summable_integral_norm hri hSn
      rw [hinter]
    simpa using hts
  have hsum0 :
    ∑' k, γ ^ k * ∫ ω, r (t + k) ω * c (s t ω) (a t ω) ∂(M θ) =
        (γ ^ 0 * ∫ ω, r (t + 0) ω * c (s t ω) (a t ω) ∂(M θ)) +
          ∑' j, γ ^ (j + 1) * ∫ ω, r (t + (j + 1)) ω * c (s t ω) (a t ω) ∂(M θ) := by
    refine Summable.tsum_eq_zero_add ?_
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (|M.env.R| * Cc')) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    have hbd' : ∀ᵐ ω ∂(M θ),
        ‖r (t + k) ω * c (s t ω) (a t ω)‖ ≤ |M.env.R| * Cc' := by
      filter_upwards [hrbd (t + k)] with ω hω
      rw [norm_mul]
      exact mul_le_mul hω (hCcle _ _) (norm_nonneg _) (abs_nonneg _)
    have hle :=
      norm_integral_le_of_norm_le_const (μ := M θ) hbd'
    have : IsProbabilityMeasure (M θ) := inferInstance
    simpa [probReal_univ, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hle (pow_nonneg h₀.1 k)
  rw [hsum0, pow_zero, one_mul, add_zero, h0, htail]
  refine (integral_add ?_ ?_).symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))
  ·
    exact Integrable.of_bound
      ((MeasurableRkd (M := M).stronglyMeasurable.mul hc).comp_measurable
        (hs.prodMk ha)).aestronglyMeasurable
      (|M.env.R| * Cc')
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_mul]
        exact mul_le_mul (NormRkd.le.Abs_R (M := M) _ _) (hCcle _ _)
          (norm_nonneg _) (abs_nonneg _))
  ·
    exact Integrable.of_bound
      ((((measurable_const.mul
          (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
            (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.V0 θ γ z.2)
            ((Measurable_Vkd.of.All_Measurable_Prob (M := M)
                (fun θ' => M.policy.measurable_prob θ') θ γ).stronglyMeasurable.comp_measurable
              measurable_snd)).measurable).stronglyMeasurable).mul hc).comp_measurable
        (hs.prodMk ha)).aestronglyMeasurable (γ * BG * Cc')
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg h₀.1]
        refine mul_le_mul ?_ (hCcle _ _) (norm_nonneg _) (mul_nonneg h₀.1 hBG)
        refine mul_le_mul_of_nonneg_left ?_ h₀.1
        have : IsProbabilityMeasure (M.env.trans (s t ω, a t ω)) := inferInstance
        simpa [probReal_univ] using
          (norm_integral_le_of_norm_le_const
            (μ := M.env.trans (s t ω, a t ω))
            (Filter.Eventually.of_forall fun y =>
              NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y)))
  · ring

/-- Vector-valued form of `integral_mul_return_eq_Qf`, obtained by pairing. -/
private lemma integral_smul_return_eq_Qf
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {ψ : 𝒮 → 𝒜 → E}
  {C : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hC : ∀ y u, ‖ψ y u‖ ≤ C)
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, (M.rkd (s t ω) (a t ω) +
        γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (s t ω, a t ω))) •
      ψ (s t ω) (a t ω) ∂(M θ) := by
-- proof
  have := M.env.reward_markov
  have := M.env.trans_markov
  set Qf : 𝒮 → 𝒜 → ℝ := fun y u =>
    M.rkd y u + γ * ∫ z, M.V0 θ γ z ∂(M.env.trans (y, u))
  set G := (γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]
  set BG : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBG : 0 ≤ BG :=
    mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hCc : 0 ≤ max C 0 := le_max_right _ _
  have hCle : ∀ y u, ‖ψ y u‖ ≤ max C 0 := fun y u => (hC y u).trans (le_max_left _ _)
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₁ t
  have ha : Measurable (a t) := Random.Measurable.of.All_Eq.snd.snd h₁ t
  have hGeq : ∀ ω, G ω = ∑' k, γ ^ k * r (t + k) ω := by
    intro ω
    simp [G, Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
  have hGbd : ∀ᵐ ω ∂(M θ), ‖G ω‖ ≤ BG := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hrω
    have hsum : Summable fun k => γ ^ k * |M.env.R| :=
      (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    have hle : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hrω (t + k))
        (pow_nonneg h₀.1 k)
    have hsn : Summable fun k => ‖γ ^ k * r (t + k) ω‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
    rw [hGeq]
    calc
      _ ≤ ∑' k, ‖γ ^ k * r (t + k) ω‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, γ ^ k * |M.env.R| := Summable.tsum_le_tsum hle hsn hsum
      _ = BG := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
  have hGm : Measurable G := by
    have hfun : G = fun ω => ∑' k, γ ^ k * r (t + k) ω := by
      ext ω
      exact hGeq ω
    rw [hfun]
    exact Measurable.tsum fun k =>
      (Random.Measurable.of.All_Eq.fst h₁ (t + k)).const_mul (γ ^ k)
  have hQfbd : ∀ y u, ‖Qf y u‖ ≤ BG := by
    intro y u
    have hR : ‖M.rkd y u‖ ≤ |M.env.R| := NormRkd.le.Abs_R (M := M) y u
    have hV : ‖∫ z, M.V0 θ γ z ∂(M.env.trans (y, u))‖ ≤ BG := by
      have : IsProbabilityMeasure (M.env.trans (y, u)) := inferInstance
      simpa [probReal_univ] using
        (norm_integral_le_of_norm_le_const
          (μ := M.env.trans (y, u))
          (Filter.Eventually.of_forall fun z =>
            NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ z))
    have : ‖Qf y u‖ ≤ |M.env.R| + γ * BG := by
      simp only [Qf]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add hR ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left hV h₀.1
    refine this.trans_eq ?_
    have hne : 1 - γ ≠ 0 := sub_ne_zero.mpr (ne_of_gt h₀.2)
    have hstep : |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) =
        (1 + γ * (1 - γ)⁻¹) * |M.env.R| := by ring
    have hinv : 1 + γ * (1 - γ)⁻¹ = (1 - γ)⁻¹ := by
      field_simp [hne]
      ring
    simp only [BG]
    rw [hstep, hinv]
  have hLint : Integrable (fun ω => G ω • ψ (s t ω) (a t ω)) (M θ) :=
    Integrable.of_bound
      (hGm.stronglyMeasurable.smul (hψ.comp_measurable (hs.prodMk ha))).aestronglyMeasurable
      (BG * max C 0)
      (Filter.Eventually.mono hGbd fun ω hω => by
        rw [norm_smul]
        exact mul_le_mul hω (hCle _ _) (norm_nonneg _) hBG)
  have hQfSM : StronglyMeasurable (Function.uncurry Qf) := by
    exact (MeasurableRkd (M := M).add (measurable_const.mul
      (StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
        (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.V0 θ γ z.2)
        ((Measurable_Vkd.of.All_Measurable_Prob (M := M)
            (fun θ' => M.policy.measurable_prob θ') θ γ).stronglyMeasurable.comp_measurable
          measurable_snd)).measurable)).stronglyMeasurable
  have hRint : Integrable (fun ω => Qf (s t ω) (a t ω) • ψ (s t ω) (a t ω)) (M θ) :=
    Integrable.of_bound
      ((hQfSM.smul hψ).comp_measurable (hs.prodMk ha)).aestronglyMeasurable
      (BG * max C 0)
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_smul]
        exact mul_le_mul (hQfbd _ _) (hCle _ _) (norm_nonneg _) hBG)
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
  intro l
  have hc : StronglyMeasurable (Function.uncurry fun y u => l (ψ y u)) :=
    l.continuous.comp_stronglyMeasurable hψ
  have hbound : ∀ y u, ‖l (ψ y u)‖ ≤ ‖l‖ * max C 0 := fun y u =>
    (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hCle y u) (norm_nonneg _))
  have hscal :=
    integral_mul_return_eq_Qf (M := M) (c := fun y u => l (ψ y u))
      (Cc := ‖l‖ * max C 0) h₀ h₁ hc hbound θ t
  have hLeq : (fun ω => l (G ω • ψ (s t ω) (a t ω))) =
      fun ω => G ω * l (ψ (s t ω) (a t ω)) := by
    funext ω
    rw [l.map_smul, smul_eq_mul]
  have hReq : (fun ω => l (Qf (s t ω) (a t ω) • ψ (s t ω) (a t ω))) =
      fun ω => Qf (s t ω) (a t ω) * l (ψ (s t ω) (a t ω)) := by
    funext ω
    rw [l.map_smul, smul_eq_mul]
  calc
    _ = ∫ ω, l (G ω • ψ (s t ω) (a t ω)) ∂(M θ) :=
      (l.integral_comp_comm hLint).symm
    _ = ∫ ω, G ω * l (ψ (s t ω) (a t ω)) ∂(M θ) := by
      rw [hLeq]
    _ = ∫ ω, Qf (s t ω) (a t ω) * l (ψ (s t ω) (a t ω)) ∂(M θ) := by
      simpa [G, Qf] using hscal
    _ = ∫ ω, l (Qf (s t ω) (a t ω) • ψ (s t ω) (a t ω)) ∂(M θ) := by
      rw [hReq]
    _ = l (∫ ω, Qf (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ)) :=
      l.integral_comp_comm hRint

/-- On a countable alphabet, a state-action score pulls out of the discounted return. -/
private lemma integral_return_smul_eq_cond
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {ψ : 𝒮 → 𝒜 → E}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hψ : ∃ C, ∀ x u, ‖ψ x u‖ ≤ C)
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, (𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s t ω ∧ a t = a t ω)) •
      ψ (s t ω) (a t ω) ∂(M θ) := by
-- proof
  classical
  obtain ⟨Cψ, hCψ⟩ := hψ
  set G := (γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]
  set Q := fun x u =>
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x ∧ a t = u)
  set BG : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBG : 0 ≤ BG :=
    mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hGbd : ∀ᵐ ω ∂(M θ), ‖G ω‖ ≤ BG := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hr
    have hsum : Summable fun k => γ ^ k * |M.env.R| :=
      (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    have hle : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hr (t + k))
        (pow_nonneg h₀.1 k)
    have hsn : Summable fun k => ‖γ ^ k * r (t + k) ω‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
    have hG : G ω = ∑' k, γ ^ k * r (t + k) ω := by
      simp [G, Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
    rw [hG]
    calc
      _ ≤ ∑' k, ‖γ ^ k * r (t + k) ω‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, γ ^ k * |M.env.R| := Summable.tsum_le_tsum hle hsn hsum
      _ = BG := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
  change ∫ ω, G ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, Q (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ)
  have hpR : Measurable (fun ω t ↦ r t ω) :=
    Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) := by
    unfold Dot.dot Function.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  let pair : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 × 𝒜 := fun ω => (s t ω, a t ω)
  have hpair : Measurable pair :=
    (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)
  have hQint : ∀ x u (_ : (M θ).map pair {(x, u)} ≠ 0),
      Q x u = ∫ ω, G ω ∂(M θ)[|pair ⁻¹' {(x, u)}] := by
    intro x u hpos
    simp only [Q, Expectation.asRV_process]
    have hpairJ : (s t, a t) = pair := by
      funext ω
      unfold JointRandomSymbol
      simp [pair]
    have hy : Measurable (s t, a t) := by
      rw [hpairJ]
      exact hpair
    have hpos' : (M θ).map (s t, a t) {(x, u)} ≠ 0 := by
      rw [hpairJ]
      exact hpos
    rw [Expectation.condEval_eq_integral hpR hy hfG hpos', hpairJ]
    simp [G, Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
  have hatom : ∀ z : 𝒮 × 𝒜, MeasurableSet (pair ⁻¹' {z}) := fun z =>
    hpair (measurableSet_singleton z)
  have hmass : ∀ z : 𝒮 × 𝒜,
      ∫ ω in pair ⁻¹' {z}, G ω ∂(M θ) = (M θ).real (pair ⁻¹' {z}) * Q z.1 z.2 := by
    intro z
    if h0 : (M θ) (pair ⁻¹' {z}) = 0 then
      rw [measureReal_def, h0, ENNReal.toReal_zero, zero_mul, Measure.restrict_eq_zero.mpr h0]
      simp
    else
      have hpos : (M θ).map pair {z} ≠ 0 := by
        rwa [Measure.map_apply hpair (measurableSet_singleton z)]
      have hQ : Q z.1 z.2 = ∫ ω, G ω ∂(M θ)[|pair ⁻¹' {z}] := by
        simpa [pair] using hQint z.1 z.2 hpos
      have hQsmul : Q z.1 z.2 =
          ((M θ) (pair ⁻¹' {z}))⁻¹.toReal • ∫ ω in pair ⁻¹' {z}, G ω ∂(M θ) := by
        rw [hQ, ProbabilityTheory.cond, integral_smul_measure]
      rw [ENNReal.toReal_inv, ← measureReal_def, smul_eq_mul] at hQsmul
      have hne : (M θ).real (pair ⁻¹' {z}) ≠ 0 := by
        rw [measureReal_def, ENNReal.toReal_ne_zero]
        exact ⟨h0, measure_ne_top (M θ) _⟩
      calc
        _ = (M θ).real (pair ⁻¹' {z}) *
              (((M θ).real (pair ⁻¹' {z}))⁻¹ * ∫ ω in pair ⁻¹' {z}, G ω ∂(M θ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
        _ = (M θ).real (pair ⁻¹' {z}) * Q z.1 z.2 := by
          rw [← hQsmul]
  have hQbd : ∀ x u (_ : (M θ).map pair {(x, u)} ≠ 0), ‖Q x u‖ ≤ BG := by
    intro x u hpos
    rw [hQint x u hpos]
    have hae : ∀ᵐ ω ∂(M θ)[|pair ⁻¹' {(x, u)}], ‖G ω‖ ≤ BG :=
      ProbabilityTheory.cond_absolutelyContinuous.ae_le hGbd
    have h0 : (M θ) (pair ⁻¹' {(x, u)}) ≠ 0 := by
      rwa [← Measure.map_apply hpair (measurableSet_singleton (x, u))]
    have : IsProbabilityMeasure (M θ)[|pair ⁻¹' {(x, u)}] :=
      ProbabilityTheory.cond_isProbabilityMeasure h0
    simpa using norm_integral_le_of_norm_le_const (μ := (M θ)[|pair ⁻¹' {(x, u)}]) hae
  have hpos_ae : ∀ᵐ ω ∂(M θ), (M θ).map pair {pair ω} ≠ 0 := by
    have hset :
        {ω | (M θ).map pair {pair ω} = 0} =
          ⋃ z : 𝒮 × 𝒜, pair ⁻¹' {z} ∩ {ω | (M θ).map pair {z} = 0} := by
      ext ω
      constructor
      · intro h
        exact Set.mem_iUnion.mpr ⟨pair ω, ⟨rfl, h⟩⟩
      · intro h
        obtain ⟨z, hz, hμ⟩ := Set.mem_iUnion.mp h
        have hz' : pair ω = z := hz
        simpa [hz'] using hμ
    apply (ae_iff.2 ?_)
    simp only [ne_eq, not_not]
    change (M θ) {ω | (M θ).map pair {pair ω} = 0} = 0
    rw [hset]
    refine measure_iUnion_null fun z => ?_
    if hz : (M θ).map pair {z} = 0 then
      have : pair ⁻¹' {z} ∩ {ω | (M θ).map pair {z} = 0} = pair ⁻¹' {z} := by
        ext ω
        simp [hz]
      rwa [this, ← Measure.map_apply hpair (measurableSet_singleton z)]
    else
      have : pair ⁻¹' {z} ∩ {ω | (M θ).map pair {z} = 0} = ∅ := by
        ext ω
        simp [hz]
      simp [this]
  have hGm : Measurable G := by
    have hfun : G = fun ω => ∑' k, γ ^ k * r (t + k) ω := by
      ext ω
      simp [G, Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
    rw [hfun]
    exact Measurable.tsum fun k => (Random.Measurable.of.All_Eq.fst h₁ (t + k)).const_mul ((γ ^ (id : ℕ → ℕ)) k)
  let F : (𝒮 × 𝒜) → (ℕ → ℝ × 𝒮 × 𝒜) → E := fun z ω =>
    (if pair ω = z then G ω else (0 : ℝ)) • ψ z.1 z.2
  let H : (𝒮 × 𝒜) → (ℕ → ℝ × 𝒮 × 𝒜) → E := fun z ω =>
    (if pair ω = z then Q z.1 z.2 else (0 : ℝ)) • ψ z.1 z.2
  have hC : ∀ x u, ‖ψ x u‖ ≤ max Cψ 0 := fun x u => (hCψ x u).trans (le_max_left _ _)
  have hFsm : ∀ z, StronglyMeasurable (F z) := by
    intro z
    have hFeq : F z = fun ω => (pair ⁻¹' {z}).indicator G ω • ψ z.1 z.2 := by
      ext ω
      if h : pair ω = z then
        simp [F, Set.indicator, h]
      else
        simp [F, Set.indicator, h]
    rw [hFeq]
    exact ((hGm.indicator (hatom z)).stronglyMeasurable).smul_const _
  have hHsm : ∀ z, StronglyMeasurable (H z) := by
    intro z
    have hHeq : H z = fun ω => (pair ⁻¹' {z}).indicator (fun _ => Q z.1 z.2) ω • ψ z.1 z.2 := by
      ext ω
      if h : pair ω = z then
        simp [H, Set.indicator, h]
      else
        simp [H, Set.indicator, h]
    rw [hHeq]
    exact (stronglyMeasurable_const.indicator (hatom z)).smul_const _
  have hFnorm : ∀ ω, ∑' z, enorm (F z ω) = enorm (G ω • ψ (s t ω) (a t ω)) := by
    intro ω
    rw [tsum_eq_single (pair ω)]
    · simp [F, pair]
    ·
      intro z hz
      simp only [F]
      rw [ite_eq_right hz.symm]
      simp
  have hHnorm : ∀ ω, ∑' z, enorm (H z ω) = enorm (Q (s t ω) (a t ω) • ψ (s t ω) (a t ω)) := by
    intro ω
    rw [tsum_eq_single (pair ω)]
    · simp [H, pair]
    ·
      intro z hz
      simp only [H]
      rw [ite_eq_right hz.symm]
      simp
  have hBd : ENNReal.ofReal (BG * max Cψ 0) * (M θ) Set.univ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (M θ) _)
  have hFtop : ∑' z, ∫⁻ ω, enorm (F z ω) ∂(M θ) ≠ ⊤ := by
    rw [← lintegral_tsum fun z => (hFsm z).aestronglyMeasurable.enorm]
    suffices ∀ᵐ ω ∂(M θ), ∑' z, enorm (F z ω) ≤ ENNReal.ofReal (BG * max Cψ 0) by
      exact ne_top_of_le_ne_top (by rwa [MeasureTheory.lintegral_const]) (lintegral_mono_ae this)
    filter_upwards [hGbd] with ω hGω
    rw [hFnorm]
    calc
      _ = enorm (G ω) * enorm (ψ (s t ω) (a t ω)) := enorm_smul _ _
      _ = ENNReal.ofReal ‖G ω‖ * ENNReal.ofReal ‖ψ (s t ω) (a t ω)‖ := by
        rw [← ofReal_norm, ← ofReal_norm]
      _ ≤ ENNReal.ofReal BG * ENNReal.ofReal (max Cψ 0) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hGω) (ENNReal.ofReal_le_ofReal (hC _ _))
      _ = ENNReal.ofReal (BG * max Cψ 0) := (ENNReal.ofReal_mul hBG).symm
  have hHtop : ∑' z, ∫⁻ ω, enorm (H z ω) ∂(M θ) ≠ ⊤ := by
    rw [← lintegral_tsum fun z => (hHsm z).aestronglyMeasurable.enorm]
    suffices ∀ᵐ ω ∂(M θ), ∑' z, enorm (H z ω) ≤ ENNReal.ofReal (BG * max Cψ 0) by
      exact ne_top_of_le_ne_top (by rwa [MeasureTheory.lintegral_const]) (lintegral_mono_ae this)
    filter_upwards [hpos_ae] with ω hωpos
    rw [hHnorm]
    calc
      _ = enorm (Q (s t ω) (a t ω)) * enorm (ψ (s t ω) (a t ω)) := enorm_smul _ _
      _ = ENNReal.ofReal ‖Q (s t ω) (a t ω)‖ * ENNReal.ofReal ‖ψ (s t ω) (a t ω)‖ := by
        rw [← ofReal_norm, ← ofReal_norm]
      _ ≤ ENNReal.ofReal BG * ENNReal.ofReal (max Cψ 0) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (hQbd (s t ω) (a t ω) (by simpa [pair] using hωpos)))
          (ENNReal.ofReal_le_ofReal (hC _ _))
      _ = ENNReal.ofReal (BG * max Cψ 0) := (ENNReal.ofReal_mul hBG).symm
  have hsumG : ∀ ω, ∑' z, F z ω = G ω • ψ (s t ω) (a t ω) := by
    intro ω
    simp [F, pair]
  have hsumQ : ∀ ω, ∑' z, H z ω = Q (s t ω) (a t ω) • ψ (s t ω) (a t ω) := by
    intro ω
    rw [tsum_eq_single (pair ω)]
    · simp [H, pair]
    ·
      intro z hz
      simp only [H]
      rw [ite_eq_right hz.symm]
      simp
  have htermF : ∀ z, ∫ ω, F z ω ∂(M θ) =
      (M θ).real (pair ⁻¹' {z}) • (Q z.1 z.2 • ψ z.1 z.2) := by
    intro z
    have hfun : (fun ω => (if pair ω = z then G ω else (0 : ℝ)) • ψ z.1 z.2) =
        fun ω => (pair ⁻¹' {z}).indicator G ω • ψ z.1 z.2 := by
      ext ω
      if h : pair ω = z then
        simp [Set.indicator, h]
      else
        simp [Set.indicator, h]
    simp only [F]
    rw [hfun, integral_smul_const, integral_indicator (hatom z), hmass z, mul_smul]
  have htermH : ∀ z, ∫ ω, H z ω ∂(M θ) =
      (M θ).real (pair ⁻¹' {z}) • (Q z.1 z.2 • ψ z.1 z.2) := by
    intro z
    have hfun : (fun ω => (if pair ω = z then Q z.1 z.2 else (0 : ℝ)) • ψ z.1 z.2) =
        fun ω => (pair ⁻¹' {z}).indicator (fun _ => Q z.1 z.2) ω • ψ z.1 z.2 := by
      ext ω
      if h : pair ω = z then
        simp [Set.indicator, h]
      else
        simp [Set.indicator, h]
    simp only [H]
    rw [hfun, integral_smul_const, integral_indicator_const _ (hatom z), smul_eq_mul, mul_smul]
  rw [integral_congr_ae (ae_of_all _ fun ω => (hsumG ω).symm),
    integral_tsum (fun z => (hFsm z).aestronglyMeasurable) hFtop,
    integral_congr_ae (ae_of_all _ fun ω => (hsumQ ω).symm),
    integral_tsum (fun z => (hHsm z).aestronglyMeasurable) hHtop]
  simp_rw [htermF, htermH]

/--
Vanilla policy-gradient theorem with action values, for a density policy:
`∇ 𝔼[r]((γ ^ id) ⬝ᵥ r) = 𝔼[s, a]((γ ^ id) ⬝ᵥ fun t ↦ Q(s[t], a[t]) • ∇ log π(a[t] | s[t]))`.

This is the continuous-action / infinite-horizon form of the finite `Model` identity: interchange
the gradient with the discounted return, unroll `fderiv V0` into a series of Bellman action-value
scores, and identify those scores with the path-conditional `Q`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {Q : Θ → ℕ → 𝒮 → 𝒜 → ℝ}
  {V : Θ → ℕ → 𝒮 → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hQ : ∀ θ t («\sf{s}» : ℕ → 𝒮) («\sf{a}» : ℕ → 𝒜), Q θ t («\sf{s}» t) («\sf{a}» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = «\sf{s}» t ∧ a t = «\sf{a}» t))
  (hV : ∀ θ t («\sf{s}» : ℕ → 𝒮), V θ t («\sf{s}» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = «\sf{s}» t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) μ.measure)
  (h₅ : sup[x] ∫ u, g x u ∂μ.measure < ∞)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : sup[y, u] ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ < ∞) :
-- imply
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      Q θ t (s t) (a t) • ∇[θ] Real.log (M.policy.prob θ (s t) (a t))) := by
-- proof
  obtain ⟨Cg, hCg⟩ := id h₅
  have h₅le : ∀ x, ∫ u, g x u ∂μ.measure ≤ Cg := fun x => hCg ⟨x, rfl⟩
  obtain ⟨Ms, hMsb⟩ := id hMs
  have hMsle : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms :=
    fun y u => hMsb ⟨(y, u), rfl⟩
  intro hrP hsP haP
  let _ := hV
  classical
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have : BorelSpace Θ := ⟨rfl⟩
  have hr : ∀ θ' t, PSpace (M θ') (r t) := fun _ t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun θ' =>
    PSpace_Path.of.All_PSpace (hr θ')
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  set BG : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBG : 0 ≤ BG :=
    mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hRint : ∀ θ' : Θ, ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ') = ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ') := by
    intro θ'
    have hrb : ∀ t, ∀ᵐ ω ∂(M θ'), ‖γ ^ t * r t ω‖ ≤ γ ^ t * |M.env.R| := fun t =>
      (All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) θ').mono fun ω h => by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left (h t) (pow_nonneg h₀.1 t)
    have hri : ∀ t, Integrable (fun ω => γ ^ t * r t ω) (M θ') := fun t =>
      Integrable.of_bound ((Random.Measurable.of.All_Eq.fst h₁ t).const_mul (γ ^ t)).aestronglyMeasurable
        _ (hrb t)
    rw [← integral_tsum_of_summable_integral_norm hri]
    · exact tsum_congr fun t => integral_const_mul _ _
    ·
      refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
      calc
        _ ≤ ∫ _, γ ^ t * |M.env.R| ∂(M θ') :=
          integral_mono_ae (hri t).norm (integrable_const _) (hrb t)
        _ = γ ^ t * |M.env.R| := by simp
  have hGet :=
    GetTSum_SMul.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ θ
  have hEfun :
    (fun θ' ↦ 𝔼[r: M θ']((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r)) =
        (fun θ' ↦ ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ')) := by
    funext θ'
    have : PSpace (M θ') (AsPathRV.path r) :=
      PSpace_Path.of.All_PSpace (hr θ')
    refine (ExpectDotPow_Id.eq.Integral_ExtDotPow_Id.of.All_EqWithDensity
      (M := M) (θ := θ') (γ := γ) (r := r)).trans ?_
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    exact hRint θ'
  have hLHS :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
        L (∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) := by
    simp only [gradient, hL]
    exact congrArg (fun f ↦ L (fderiv ℝ f θ)) hEfun ▸
      congrArg L hGet.fderiv.symm ▸ rfl
  have hTSum :=
    TSum_SMul.eq.Integral_Fderiv_Vkd.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ θ
  have hQkd :=
    Integral_Fderiv_Vkd.eq.TSum_SMul_Integral_SMul_Qkd_FderivLog.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_Eq_Joint.All_EqWithDensity
      (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ hφ hMs
  set ψ : 𝒮 → 𝒜 → Θ →L[ℝ] ℝ := fun y u =>
    fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ
  have hψ : StronglyMeasurable (Function.uncurry ψ) := hφ
  have hMs0 : ∀ y u, ‖ψ y u‖ ≤ max Ms 0 := fun y u => (hMsle y u).trans (le_max_left _ _)
  have hs_meas : ∀ t, Measurable (s t) := fun t =>
    Random.Measurable.of.All_Eq.snd.fst h₁ t
  have ha_meas : ∀ t, Measurable (a t) := fun t =>
    Random.Measurable.of.All_Eq.snd.snd h₁ t
  have hident : ∀ t,
      integral (μ := M θ) (fun ω =>
        (M.rkd (s t ω) (a t ω) +
            γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (s t ω, a t ω))) •
          ψ (s t ω) (a t ω)) =
        integral (μ := M θ) (fun ω => Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω)) := by
    intro t
    have hret :=
      integral_smul_return_eq_Qf (M := M) (ψ := ψ) (C := max Ms 0)
        h₀ h₁ hψ (fun y u => hMs0 y u) θ t
    have hcond :=
      integral_return_smul_eq_cond (M := M) (r := r) (s := s) (a := a) (ψ := ψ)
        h₀ h₁ ⟨max Ms 0, fun y u => hMs0 y u⟩ θ t
    refine hret.symm.trans (hcond.trans (integral_congr_ae (ae_of_all _ fun ω => ?_)))
    have hq := hQ θ t (fun _ => s t ω) (fun _ => a t ω)
    simp [hq, Expectation.asRV, AsPathRV.path_fun]
  have hchain :
    ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
        ∑' t, γ ^ t • integral (μ := M θ) (fun ω =>
          Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω)) :=
    hTSum.trans (hQkd.trans (tsum_congr fun t => congrArg (fun z => γ ^ t • z) (hident t)))
  have hgradSm : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)) := by
    simp only [gradient]
    exact L.continuous.comp_stronglyMeasurable hφ
  have hQB : ∀ t x u (_ : (M θ).map (fun ω => (s t ω, a t ω)) {(x, u)} ≠ 0),
      ‖Q θ t x u‖ ≤ BG := by
    intro t x u
    have hpR : Measurable (fun ω t ↦ r t ω) :=
      Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
    have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ ({ toFun := integ } : Fun ℕ ℝ)[t:]) := by
      unfold Dot.dot Fun.getSliceFrom
      refine Measurable.tsum fun k => ?_
      have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
      simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
    have hsa : Measurable (fun ω => (s t ω, a t ω)) :=
      (hs_meas t).prodMk (ha_meas t)
    have hsaJ : (s t, a t) = fun ω => (s t ω, a t ω) := by
      funext ω
      unfold JointRandomSymbol
      rfl
    have hy : Measurable (s t, a t) := by
      rw [hsaJ]
      exact hsa
    have hQint (hpos : (M θ).map (fun ω => (s t ω, a t ω)) {(x, u)} ≠ 0) :
      Q θ t x u = ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω
        ∂(M θ)[|(fun ω => (s t ω, a t ω)) ⁻¹' {(x, u)}] := by
      rw [hQ θ t (fun _ => x) (fun _ => u)]
      simp only [Expectation.asRV, AsPathRV.path_fun]
      have hpos' : (M θ).map (s t, a t) {(x, u)} ≠ 0 := by
        rw [hsaJ]
        exact hpos
      rw [Expectation.condEval_eq_integral hpR hy hfG hpos', hsaJ]
      simp [Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
    have hGbd : ∀ᵐ ω ∂(M θ), ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ BG := by
      filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hrω
      have hsum : Summable fun k => γ ^ k * |M.env.R| :=
        (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
      have hle : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hrω (t + k))
          (pow_nonneg h₀.1 k)
      have hsn : Summable fun k => ‖γ ^ k * r (t + k) ω‖ :=
        Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
      have hG : ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω = ∑' k, γ ^ k * r (t + k) ω := by
        simp [Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
      rw [hG]
      calc
        _ ≤ ∑' k, ‖γ ^ k * r (t + k) ω‖ := norm_tsum_le_tsum_norm hsn
        _ ≤ ∑' k, γ ^ k * |M.env.R| := Summable.tsum_le_tsum hle hsn hsum
        _ = BG := by
          rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
    intro hpos
    have h0 : (M θ) ((fun ω => (s t ω, a t ω)) ⁻¹' {(x, u)}) ≠ 0 := by
      rwa [← Measure.map_apply hsa (measurableSet_singleton (x, u))]
    rw [hQint hpos]
    have hae : ∀ᵐ ω ∂(M θ)[|(fun ω => (s t ω, a t ω)) ⁻¹' {(x, u)}],
        ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ BG :=
      cond_absolutelyContinuous.ae_le hGbd
    have : IsProbabilityMeasure
      (M θ)[|(fun ω => (s t ω, a t ω)) ⁻¹' {(x, u)}] :=
      cond_isProbabilityMeasure h0
    simpa using
      norm_integral_le_of_norm_le_const
        (μ := (M θ)[|(fun ω => (s t ω, a t ω)) ⁻¹' {(x, u)}]) hae
  have hpos_ae_t : ∀ t, ∀ᵐ ω ∂(M θ),
      (M θ).map (fun ω => (s t ω, a t ω)) {(s t ω, a t ω)} ≠ 0 := by
    intro t
    let pair : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 × 𝒜 := fun ω => (s t ω, a t ω)
    have hpair : Measurable pair := (hs_meas t).prodMk (ha_meas t)
    have hset :
        {ω | (M θ).map pair {pair ω} = 0} =
          ⋃ z : 𝒮 × 𝒜, pair ⁻¹' {z} ∩ {ω | (M θ).map pair {z} = 0} := by
      ext ω
      constructor
      · intro h
        exact Set.mem_iUnion.mpr ⟨pair ω, ⟨rfl, h⟩⟩
      · intro h
        obtain ⟨z, hz, hμ⟩ := Set.mem_iUnion.mp h
        have hz' : pair ω = z := hz
        simpa [hz'] using hμ
    apply (ae_iff.2 ?_)
    simp only [ne_eq, not_not]
    change (M θ) {ω | (M θ).map pair {pair ω} = 0} = 0
    rw [hset]
    refine measure_iUnion_null fun z => ?_
    if hz : (M θ).map pair {z} = 0 then
      have : pair ⁻¹' {z} ∩ {ω | (M θ).map pair {z} = 0} = pair ⁻¹' {z} := by
        ext ω
        simp [hz]
      rwa [this, ← Measure.map_apply hpair (measurableSet_singleton z)]
    else
      have : pair ⁻¹' {z} ∩ {ω | (M θ).map pair {z} = 0} = ∅ := by
        ext ω
        simp [hz]
      simp [this]
  have hQterm_sm : ∀ t, StronglyMeasurable fun ω =>
      Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) := fun t =>
    (StronglyMeasurable.of_discrete (f := fun q : 𝒮 × 𝒜 => Q θ t q.1 q.2 • ψ q.1 q.2)).comp_measurable
      ((hs_meas t).prodMk (ha_meas t))
  have hQFint_dual : ∀ t, Integrable (fun ω =>
      Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω)) (M θ) := fun t =>
    Integrable.of_bound (hQterm_sm t).aestronglyMeasurable (BG * max Ms 0)
      (by
        filter_upwards [hpos_ae_t t] with ω hωpos
        rw [norm_smul]
        exact mul_le_mul (hQB t (s t ω) (a t ω) hωpos) (hMs0 (s t ω) (a t ω))
          (norm_nonneg _) hBG)
  have hQFint : ∀ t, Integrable (fun ω =>
      γ ^ t • Q θ t (s t ω) (a t ω) •
        ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))) (M θ) := by
    intro t
    have hsm : StronglyMeasurable fun ω =>
        Q θ t (s t ω) (a t ω) • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) :=
      (StronglyMeasurable.of_discrete
        (f := fun q : 𝒮 × 𝒜 =>
          Q θ t q.1 q.2 • ∇[θ] Real.log (M.policy.prob θ q.1 q.2))).comp_measurable
        ((hs_meas t).prodMk (ha_meas t))
    refine Integrable.of_bound (hsm.const_smul (γ ^ t)).aestronglyMeasurable
      (γ ^ t * (BG * max Ms 0)) ?_
    filter_upwards [hpos_ae_t t] with ω hωpos
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t), norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 t)
    refine mul_le_mul (hQB t (s t ω) (a t ω) hωpos) ?_ (norm_nonneg _) hBG
    simp only [gradient]
    rw [LinearIsometryEquiv.norm_map]
    exact hMs0 (s t ω) (a t ω)
  have hsummable :
    Summable (fun t => γ ^ t • integral (μ := M θ) (fun ω =>
        Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω))) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (BG * max Ms 0)) fun t => ?_
    set I := integral (μ := M θ) (fun ω =>
      Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω))
    have hnorm : ‖γ ^ t • I‖ = γ ^ t * ‖I‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h₀.1 t)]
    rw [hnorm]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 t)
    have : IsProbabilityMeasure (M θ) := inferInstance
    simpa [probReal_univ] using
      (norm_integral_le_of_norm_le_const (μ := M θ)
        (by
          filter_upwards [hpos_ae_t t] with ω hωpos
          rw [norm_smul (Q θ t (s t ω) (a t ω)) (ψ (s t ω) (a t ω)),
            Real.norm_eq_abs]
          exact mul_le_mul (hQB t (s t ω) (a t ω) hωpos) (hMs0 (s t ω) (a t ω))
            (norm_nonneg _) hBG))
  have hLtsum :
    L (∑' t, γ ^ t • integral (μ := M θ) (fun ω =>
          Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω))) =
        ∑' t, γ ^ t • integral (μ := M θ) (fun ω =>
          Q θ t (s t ω) (a t ω) • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))) := by
    have hmap := L.toContinuousLinearMap.map_tsum hsummable
    refine hmap.trans (tsum_congr fun t => ?_)
    set I := integral (μ := M θ) (fun ω =>
      Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω))
    have hsmul : (L : StrongDual ℝ Θ → Θ) (γ ^ t • I) = γ ^ t • L I :=
      map_smul (L : StrongDual ℝ Θ →L[ℝ] Θ) (γ ^ t) I
    refine hsmul.trans ?_
    congr 1
    have hinter :=
      L.integral_comp_comm (μ := M θ)
        (fun ω => Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω))
    refine hinter.symm.trans (integral_congr_ae (ae_of_all _ fun ω => ?_))
    simp only [ψ, gradient, hL]
    exact map_smul (L : StrongDual ℝ Θ →L[ℝ] Θ)
      (Q θ t (s t ω) (a t ω))
      (fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ)
  have hQsum : Summable fun t => ∫ ω, ‖γ ^ t •
      Q θ t (s t ω) (a t ω) • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun t => ?_) ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (BG * max Ms 0))
    have hgrad : ∀ ω, ‖∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))‖ ≤ max Ms 0 := fun ω => by
      simp only [gradient]
      rw [LinearIsometryEquiv.norm_map]
      exact hMs0 (s t ω) (a t ω)
    calc
      _ ≤ ∫ _, γ ^ t * (BG * max Ms 0) ∂(M θ) :=
        integral_mono_ae (hQFint t).norm (integrable_const _)
          (by
            filter_upwards [hpos_ae_t t] with ω hωpos
            rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t), norm_smul]
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg h₀.1 t)
            exact mul_le_mul (hQB t (s t ω) (a t ω) hωpos) (hgrad ω) (norm_nonneg _) hBG)
      _ = γ ^ t * (BG * max Ms 0) := by
        rw [MeasureTheory.integral_const]
        simp [probReal_univ, smul_eq_mul]
  have hRHS_tsum :
    integral (μ := M θ) (fun ω =>
        ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
          Q θ t (s t ω) (a t ω) • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)))) =
      ∑' t, γ ^ t • integral (μ := M θ) (fun ω =>
        Q θ t (s t ω) (a t ω) • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))) := by
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    rw [← integral_tsum_of_summable_integral_norm hQFint hQsum]
    refine tsum_congr fun t => integral_smul (γ ^ t) _
  have hRHS_sm : AEStronglyMeasurable
    (fun p : (ℕ → 𝒮) × (ℕ → 𝒜) =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        Q θ t (p.1 t) (p.2 t) • ∇[θ] Real.log (M.policy.prob θ (p.1 t) (p.2 t)))
    ((M θ).map (AsPathRV.path s, AsPathRV.path a)) := by
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    refine (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t => ?_).aestronglyMeasurable
    exact StronglyMeasurable.comp_measurable
      (f := fun q : 𝒮 × 𝒜 ↦
        γ ^ t • Q θ t q.1 q.2 • ∇[θ] Real.log (M.policy.prob θ q.1 q.2))
      StronglyMeasurable.of_discrete
      (show Measurable fun p : (ℕ → 𝒮) × (ℕ → 𝒜) ↦ (p.1 t, p.2 t) from
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          ((measurable_pi_apply t).comp measurable_snd))
  refine hLHS.trans ((congrArg L hchain).trans (hLtsum.trans (hRHS_tsum.symm.trans ?_)))
  refine ((OfRV.eq.Integral.of.AEStronglyMeasurable_Map hRHS_sm).trans ?_).symm
  simp only [JointRandomSymbol, AsPathRV.path]


-- created on 2026-11-11
-- updated on 2026-11-14
