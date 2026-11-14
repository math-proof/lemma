import Lemma.Random.SubAddKfMul_KfKf.eq.Zero.of.In_Ico.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Theorem.Probability.CondExpectation
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Kf.eq.Integral.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.NormWkd.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real Finset Filter Kernel
set_option maxHeartbeats 800000


private lemma stage_clip
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {θ : Θ} (y : 𝒮) :
  ∫ w, clip w.1 (-M.env.R) M.env.R ∂(M.stageK θ y) = M.Wkd θ 0 y := by
  have := M.env.reward_markov
  have hf : StronglyMeasurable fun w : ℝ × 𝒮 × 𝒜 ↦ clip w.1 (-M.env.R) M.env.R :=
    ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ (w : ℝ × 𝒮 × 𝒜), ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  have e :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ y
  refine e.trans ?_
  simp only [DensityModel.Wkd, DensityModel.rkd, smul_eq_mul]

private lemma integral_Kf_clip_stage
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {θ : Θ} (j : ℕ) (x : 𝒮) :
  ∫ z, M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j z ∂(M.stageK θ x) =
    M.Wkd θ j x := by
  have := M.env.reward_markov
  have := M.env.trans_markov
  have hf : StronglyMeasurable fun w : ℝ × 𝒮 × 𝒜 ↦ clip w.1 (-M.env.R) M.env.R :=
    ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ (w : ℝ × 𝒮 × 𝒜), ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  induction j generalizing x with
  | zero =>
    exact stage_clip (M := M) (θ := θ) x
  | succ j ih =>
    have hKf :=
      StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ j
    have hsm : StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 ↦
        M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) (j + 1) z :=
      (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ (j + 1)).1
    have hbd : ∀ z, ‖M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) (j + 1) z‖ ≤ |M.env.R| :=
      (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ (j + 1)).2
    have hKf1 : ∀ z,
        M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) (j + 1) z =
          ∫ w, M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j w ∂(M.K θ z) :=
      fun z => Kf.eq.Integral.All_EqWithDensity (M := M) θ j z
    have eS :=
      Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hsm hbd θ x
    have hKindep : ∀ ρ u,
        M.K θ (ρ, x, u) = M.stageK θ ∘ₘ M.env.trans (x, u) := by
      intro ρ u
      unfold DensityModel.K
      rw [Kernel.comp_apply, Kernel.comap_apply]
    have hρ : ∀ u,
        ∫ ρ, M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) (j + 1) (ρ, x, u)
          ∂(M.env.reward (x, u)) =
          ∫ y, M.Wkd θ j y ∂(M.env.trans (x, u)) := by
      intro u
      have : IsProbabilityMeasure (M.env.reward (x, u)) := inferInstance
      have hconst :
          (λ ρ => M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) (j + 1) (ρ, x, u)) =
            fun _ => ∫ w, M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j w
              ∂(M.stageK θ ∘ₘ M.env.trans (x, u)) := by
        funext ρ
        rw [hKf1, hKindep]
      have hbind :
          Integrable (M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j)
            (M.stageK θ ∘ₘ M.env.trans (x, u)) :=
        Integrable.of_bound hKf.1.aestronglyMeasurable _ (Filter.Eventually.of_forall hKf.2)
      rw [hconst, MeasureTheory.integral_const, probReal_univ, one_smul,
        Integral.eq.Integral_Integral.of.Integrable_Bind hbind]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => ih y)
    refine eS.trans ?_
    change ∫ u, M.policy.prob θ x u •
        (∫ ρ, M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) (j + 1) (ρ, x, u)
          ∂(M.env.reward (x, u)))
        ∂ReferenceMeasure.measure = _
    simp_rw [hρ, smul_eq_mul]
    simp only [DensityModel.Wkd]

private lemma integral_phi_r_eq_Wkd
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {φ : 𝒮 → ℝ} {Cφ : ℝ}
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hφ : StronglyMeasurable φ)
  (hφC : ∀ x, ‖φ x‖ ≤ Cφ)
  (θ : Θ) (k j : ℕ) :
  ∫ ω, φ (s k ω) * r (k + j) ω ∂(M θ) =
    ∫ x, φ x * M.Wkd θ j x ∂((M θ).map (s k)) := by
  have := M.env.reward_markov
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  have hCφ0 : 0 ≤ max Cφ 0 := le_max_right _ _
  have hφC' : ∀ x, ‖φ x‖ ≤ max Cφ 0 := fun x => (hφC x).trans (le_max_left _ _)
  have hfclip : StronglyMeasurable fun w : ℝ × 𝒮 × 𝒜 =>
      clip w.1 (-M.env.R) M.env.R :=
    ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hCclip : ∀ (w : ℝ × 𝒮 × 𝒜),
      ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun w => NormClip.le.Abs_R M.env.R w.1
  have hclip := MEq_Clip.of.All_Eq.All_EqWithDensity h₀ (M := M) θ (k + j)
  have hae : (fun ω => φ (s k ω) * r (k + j) ω) =ᵐ[M θ]
      fun ω => φ (s k ω) * clip (ω (k + j)).1 (-M.env.R) M.env.R := by
    filter_upwards [hclip] with ω hω
    rw [hω]
  have e1 := integral_congr_ae hae
  let G : (Π _ : Finset.Iic k, ℝ × 𝒮 × 𝒜) → ℝ :=
    fun h => φ (h ⟨k, Finset.mem_Iic.2 le_rfl⟩).2.1
  have hG : StronglyMeasurable G :=
    hφ.comp_measurable (measurable_snd.fst.comp (measurable_pi_apply _))
  have hCG : ∀ h, ‖G h‖ ≤ max Cφ 0 := fun h => hφC' _
  have e2 :=
    All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hfclip hCclip θ j k hG hCG
  have e3 :
      ∫ ω, φ (s k ω) * clip (ω (k + j)).1 (-M.env.R) M.env.R ∂(M θ) =
        ∫ ω, G (Preorder.frestrictLe k ω) * clip (ω (k + j)).1 (-M.env.R) M.env.R ∂(M θ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => rfl)
  have hKf :=
    StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hfclip hCclip θ j
  have hfun : StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 =>
      φ z.2.1 * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j z :=
    (hφ.comp_measurable measurable_snd.fst).mul hKf.1
  have hfunC : ∀ z,
      ‖φ z.2.1 * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j z‖ ≤
        max Cφ 0 * |M.env.R| := fun z => by
    rw [norm_mul]
    exact mul_le_mul (hφC' _) (hKf.2 z) (norm_nonneg _) hCφ0
  have e4 :
      ∫ ω, G (Preorder.frestrictLe k ω) *
          M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j (ω k) ∂(M θ) =
        ∫ z, φ z.2.1 * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j z
          ∂((M θ).map (fun ω => ω k)) := by
    have := integral_map (μ := M θ) (measurable_pi_apply k).aemeasurable
      (f := fun z : ℝ × 𝒮 × 𝒜 =>
        φ z.2.1 * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j z)
      (hfun.aestronglyMeasurable)
    simpa [G, s] using this.symm
  have hmap := Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₀ θ k
  have hbind :
      Integrable (fun z => φ z.2.1 * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j z)
        (M.stageK θ ∘ₘ (M θ).map (s k)) :=
    Integrable.of_bound hfun.aestronglyMeasurable _ (Filter.Eventually.of_forall hfunC)
  have hx : ∀ x,
      ∫ z, φ z.2.1 * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j z ∂(M.stageK θ x) =
        φ x * M.Wkd θ j x := by
    intro x
    have eS :=
      Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hfun hfunC θ x
    have eS0 :=
      Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hKf.1 hKf.2 θ x
    have hinner : ∀ u,
        ∫ ρ, φ x * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j (ρ, x, u)
          ∂(M.env.reward (x, u)) =
          φ x * ∫ ρ, M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j (ρ, x, u)
            ∂(M.env.reward (x, u)) := fun u =>
      integral_const_mul _ _
    refine eS.trans ?_
    change ∫ u, M.policy.prob θ x u •
        (∫ ρ, φ x * M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j (ρ, x, u)
          ∂(M.env.reward (x, u)))
        ∂ReferenceMeasure.measure = _
    simp_rw [hinner]
    have hscale : ∀ u,
        M.policy.prob θ x u •
          (φ x * ∫ ρ, M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j (ρ, x, u)
            ∂(M.env.reward (x, u))) =
          φ x * (M.policy.prob θ x u •
            ∫ ρ, M.Kf θ (fun w ↦ clip w.1 (-M.env.R) M.env.R) j (ρ, x, u)
              ∂(M.env.reward (x, u))) := fun u => by
      simp [smul_eq_mul]; ring
    simp_rw [smul_eq_mul] at hscale eS0 ⊢
    simp_rw [hscale]
    rw [integral_const_mul, ← eS0, integral_Kf_clip_stage]
  refine e1.trans (e3.trans (e2.trans (e4.trans ?_)))
  rw [hmap, Integral.eq.Integral_Integral.of.Integrable_Bind hbind]
  exact integral_congr_ae (Filter.Eventually.of_forall hx)

/--
The discounted series value `V0 θ γ` is a version of the σ-algebra conditional
expected return: `V0 θ γ (s k) =ᵐ 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[k:] | s k)`.
This holds pathwise almost everywhere, with no atom-mass hypothesis on `s k`
(the state space need not be discrete).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (θ : Θ)
  (k : ℕ) :
-- imply
  (fun ω => M.V0 θ γ (s k ω)) =ᵐ[M θ]
    Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
      (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := by
-- proof
  classical
  have hs : Measurable (s k) := Random.Measurable.of.All_Eq.snd.fst h₁ k
  have hrm : ∀ j, Measurable (r j) := fun j => Random.Measurable.of.All_Eq.fst h₁ j
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfGret : Measurable
      (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) :=
    Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
  have hret : Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] :=
    hfGret.comp hpR
  set BV : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBV0 : 0 ≤ BV :=
    mul_nonneg (inv_nonneg.2 (le_of_lt (sub_pos.2 hγ.2))) (abs_nonneg _)
  have hr_bd : ∀ᵐ ω ∂(M θ), ∀ j, |r j ω| ≤ |M.env.R| := by
    have hcl : ∀ j, r j =ᵐ[M θ] fun ω => clip (ω j).1 (-M.env.R) M.env.R :=
      fun j => MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ j
    have hcl' : ∀ᵐ ω ∂(M θ), ∀ j,
        r j ω = clip (ω j).1 (-M.env.R) M.env.R :=
      (ae_all_iff (ι := ℕ)).mpr hcl
    filter_upwards [hcl'] with ω hω j
    rw [hω j, ← Real.norm_eq_abs]
    exact NormClip.le.Abs_R (R := M.env.R) (ρ := (ω j).1)
  have hret_bd : ∀ᵐ ω ∂(M θ), ∀ k',
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k':])‖ ≤ BV := by
    have hgeo := (hasSum_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|
    filter_upwards [hr_bd] with ω hω k'
    refine tsum_of_norm_bounded hgeo fun j => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) j = γ ^ j := rfl
    have hslice : (fun i => r i ω)[k':] j = r (k' + j) ω := rfl
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω (k' + j)) (pow_nonneg hγ.1 j)
  have hGi : Integrable
      (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) (M θ) :=
    Integrable.of_bound hret.aestronglyMeasurable BV
      (by filter_upwards [hret_bd] with ω hω; exact hω k)
  have hV0m : Measurable (M.V0 θ γ) :=
    Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ
  have hV0s : Measurable fun ω => M.V0 θ γ (s k ω) := hV0m.comp hs
  have hV0bd : ∀ ω, ‖M.V0 θ γ (s k ω)‖ ≤ BV := fun ω =>
    NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) hγ θ (s k ω)
  have hV0i : Integrable (fun ω => M.V0 θ γ (s k ω)) (M θ) :=
    Integrable.of_bound hV0s.aestronglyMeasurable BV (Filter.Eventually.of_forall hV0bd)
  have hm : MeasurableSpace.comap (s k) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ × 𝒮 × 𝒜)) :=
    hs.comap_le
  have hdot : ∀ ω,
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] =
        ∑' j, γ ^ j * r (k + j) ω := fun ω => rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hGi
    (fun _ _ _ => hV0i.integrableOn) ?_ ?_)
  · rintro t ⟨B, hB, rfl⟩ _
    let φ : 𝒮 → ℝ := B.indicator fun _ => (1 : ℝ)
    have hφ : StronglyMeasurable φ :=
      (measurable_const.indicator hB).stronglyMeasurable
    have hφC : ∀ x, ‖φ x‖ ≤ (1 : ℝ) := fun x => by
      change ‖B.indicator (fun _ : 𝒮 => (1 : ℝ)) x‖ ≤ 1
      by_cases hx : x ∈ B
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx]
    have hWm : ∀ j, Measurable (M.Wkd θ j) := fun j =>
      Measurable_Wkd.of.All_Measurable_Prob hπ θ j
    have hWbd : ∀ j x, ‖M.Wkd θ j x‖ ≤ |M.env.R| := fun j x =>
      NormWkd.le.Abs_R (M := M) θ j x
    have hL :
        ∫ ω in s k ⁻¹' B, M.V0 θ γ (s k ω) ∂(M θ) =
          ∫ x, φ x * M.V0 θ γ x ∂((M θ).map (s k)) := by
      have e := setIntegral_map (s := B) hB
        (f := M.V0 θ γ) (μ := M θ) (g := s k)
        hV0m.aestronglyMeasurable hs.aemeasurable
      refine e.symm.trans ?_
      rw [← integral_indicator hB]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [Set.indicator, φ]
    have hR :
        ∫ ω in s k ⁻¹' B,
            (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] ∂(M θ) =
          ∫ ω, φ (s k ω) *
            ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) ∂(M θ) := by
      rw [← integral_indicator (hs hB)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      by_cases hω : s k ω ∈ B <;> simp [Set.indicator, φ, hω]
    -- finish by identifying both sides with the Wkd series after tsum interchange
    have hV0series : (fun x => M.V0 θ γ x) =
        fun x => ∑' j, γ ^ j * M.Wkd θ j x := funext fun _ => rfl
    have htermR : ∀ j, Integrable
        (fun ω => φ (s k ω) * (γ ^ j * r (k + j) ω)) (M θ) := fun j => by
      have hsmul : StronglyMeasurable fun ω => φ (s k ω) * (γ ^ j * r (k + j) ω) :=
        (hφ.comp_measurable hs).mul ((hrm (k + j)).const_mul (γ ^ j)).stronglyMeasurable
      refine Integrable.of_bound hsmul.aestronglyMeasurable (γ ^ j * |M.env.R|) ?_
      filter_upwards [hr_bd] with ω hω
      have h1 : ‖φ (s k ω) * (γ ^ j * r (k + j) ω)‖ ≤
          ‖φ (s k ω)‖ * (γ ^ j * |r (k + j) ω|) := by
        rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1, Real.norm_eq_abs, Real.norm_eq_abs]
      have h2 : ‖φ (s k ω)‖ * (γ ^ j * |r (k + j) ω|) ≤ 1 * (γ ^ j * |M.env.R|) :=
        mul_le_mul (hφC _) (mul_le_mul_of_nonneg_left (hω (k + j)) (pow_nonneg hγ.1 j))
          (mul_nonneg (pow_nonneg hγ.1 j) (abs_nonneg _)) (by exact zero_le_one)
      simpa using h1.trans h2
    have hsumR : Summable fun j =>
        ∫ ω, ‖φ (s k ω) * (γ ^ j * r (k + j) ω)‖ ∂(M θ) := by
      refine Summable.of_nonneg_of_le
        (fun j => integral_nonneg fun _ => norm_nonneg _) (fun j => ?_)
        ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|)
      have hintc : Integrable (fun _ => γ ^ j * |M.env.R|) (M θ) := integrable_const _
      have : ∫ ω, ‖φ (s k ω) * (γ ^ j * r (k + j) ω)‖ ∂(M θ) ≤
          ∫ ω, γ ^ j * |M.env.R| ∂(M θ) := by
        apply integral_mono_ae (htermR j).norm hintc
        filter_upwards [hr_bd] with ω hω
        have h1 : ‖φ (s k ω) * (γ ^ j * r (k + j) ω)‖ ≤
            ‖φ (s k ω)‖ * (γ ^ j * |r (k + j) ω|) := by
          rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1, Real.norm_eq_abs, Real.norm_eq_abs]
        have h2 : ‖φ (s k ω)‖ * (γ ^ j * |r (k + j) ω|) ≤ 1 * (γ ^ j * |M.env.R|) :=
          mul_le_mul (hφC _) (mul_le_mul_of_nonneg_left (hω (k + j)) (pow_nonneg hγ.1 j))
            (mul_nonneg (pow_nonneg hγ.1 j) (abs_nonneg _)) (by exact zero_le_one)
        simpa using h1.trans h2
      refine this.trans ?_
      simp
    have htermW : ∀ j, Integrable (fun x => φ x * (γ ^ j * M.Wkd θ j x))
        ((M θ).map (s k)) := fun j => by
      have hsm : StronglyMeasurable fun x => φ x * (γ ^ j * M.Wkd θ j x) :=
        hφ.mul ((hWm j).const_mul (γ ^ j)).stronglyMeasurable
      refine Integrable.of_bound hsm.aestronglyMeasurable (γ ^ j * |M.env.R|)
        (Filter.Eventually.of_forall fun x => by
          have h1 : ‖φ x * (γ ^ j * M.Wkd θ j x)‖ ≤
              ‖φ x‖ * (γ ^ j * ‖M.Wkd θ j x‖) := by
            rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
          have h2 : ‖φ x‖ * (γ ^ j * ‖M.Wkd θ j x‖) ≤ 1 * (γ ^ j * |M.env.R|) :=
            mul_le_mul (hφC x)
              (mul_le_mul_of_nonneg_left (hWbd j x) (pow_nonneg hγ.1 j))
              (mul_nonneg (pow_nonneg hγ.1 j) (norm_nonneg _)) (by exact zero_le_one)
          simpa using h1.trans h2)
    have hsumW : Summable fun j =>
        ∫ x, ‖φ x * (γ ^ j * M.Wkd θ j x)‖ ∂((M θ).map (s k)) := by
      refine Summable.of_nonneg_of_le
        (fun j => integral_nonneg fun _ => norm_nonneg _) (fun j => ?_)
        ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|)
      have : ∫ x, ‖φ x * (γ ^ j * M.Wkd θ j x)‖ ∂((M θ).map (s k)) ≤
          ∫ x, γ ^ j * |M.env.R| ∂((M θ).map (s k)) := by
        apply integral_mono_ae (htermW j).norm (integrable_const _)
        refine Filter.Eventually.of_forall fun x => ?_
        have h1 : ‖φ x * (γ ^ j * M.Wkd θ j x)‖ ≤
            ‖φ x‖ * (γ ^ j * ‖M.Wkd θ j x‖) := by
          rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
        have h2 : ‖φ x‖ * (γ ^ j * ‖M.Wkd θ j x‖) ≤ 1 * (γ ^ j * |M.env.R|) :=
          mul_le_mul (hφC x)
            (mul_le_mul_of_nonneg_left (hWbd j x) (pow_nonneg hγ.1 j))
            (mul_nonneg (pow_nonneg hγ.1 j) (norm_nonneg _)) (by exact zero_le_one)
        simpa using h1.trans h2
      refine this.trans ?_
      simp
    have hswapR :
        ∫ ω, φ (s k ω) *
            ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) ∂(M θ) =
          ∑' j, ∫ ω, φ (s k ω) * (γ ^ j * r (k + j) ω) ∂(M θ) := by
      have e := integral_tsum_of_summable_integral_norm (F := fun j ω =>
        φ (s k ω) * (γ ^ j * r (k + j) ω)) htermR hsumR
      refine Eq.trans ?_ e.symm
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp [hdot, ← tsum_mul_left]
    have hswapW :
        ∫ x, φ x * M.V0 θ γ x ∂((M θ).map (s k)) =
          ∑' j, ∫ x, φ x * (γ ^ j * M.Wkd θ j x) ∂((M θ).map (s k)) := by
      have e := integral_tsum_of_summable_integral_norm (F := fun j x =>
        φ x * (γ ^ j * M.Wkd θ j x)) htermW hsumW
      refine Eq.trans ?_ e.symm
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [hV0series, ← tsum_mul_left]
    have hterm_eq : ∀ j,
        ∫ ω, φ (s k ω) * (γ ^ j * r (k + j) ω) ∂(M θ) =
          ∫ x, φ x * (γ ^ j * M.Wkd θ j x) ∂((M θ).map (s k)) := fun j => by
      have e := integral_phi_r_eq_Wkd (M := M) h₁ hφ hφC θ k j
      have e' :
          ∫ ω, φ (s k ω) * (γ ^ j * r (k + j) ω) ∂(M θ) =
            γ ^ j * ∫ ω, φ (s k ω) * r (k + j) ω ∂(M θ) := by
        simp_rw [mul_left_comm (φ (_))]
        exact integral_const_mul _ _
      have e'' :
          ∫ x, φ x * (γ ^ j * M.Wkd θ j x) ∂((M θ).map (s k)) =
            γ ^ j * ∫ x, φ x * M.Wkd θ j x ∂((M θ).map (s k)) := by
        simp_rw [mul_left_comm (φ _)]
        exact integral_const_mul _ _
      rw [e', e'', e]
    rw [hL, hR, hswapW, hswapR]
    exact tsum_congr fun j => (hterm_eq j).symm
  · exact (hV0m.comp (comap_measurable (s k))).stronglyMeasurable.aestronglyMeasurable


-- created on 2026-11-12
