import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_EqWithDensity
import Lemma.Random.Map.eq.BindK.of.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.EqMapStageK_12.of.All_EqWithDensity
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Kernel
set_option maxHeartbeats 400000


private lemma map_s0_eq_init
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
  (M.traj θ).map (s 0) = (M.init : Measure _) := by
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  have : (M.traj θ).map (s 0) = ((M.traj θ).map (fun ω ↦ ω 0)).map (fun z ↦ z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply 0)]; rfl
  rw [this, Map.eq.BindStageK.of.All_EqWithDensity,
    EqMapStageK_12.of.All_EqWithDensity]

/-- `κ.comap f ∘ₘ μ = κ ∘ₘ (μ.map f)`. -/
private lemma comp_comap_eq_comp_map
  {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (κ : Kernel β γ) [IsSFiniteKernel κ] (μ : Measure α) [SFinite μ]
  {f : α → β} (hf : Measurable f) :
  κ.comap f hf ∘ₘ μ = κ ∘ₘ (μ.map f) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Kernel.comap_apply]
  exact (lintegral_map (κ.measurable_coe hs) hf).symm

private lemma map_s_succ
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
  (M.traj θ).map (s (t + 1)) =
    M.transK ∘ₘ (M.traj θ).map (fun ω ↦ (s t ω, a t ω)) := by
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  set μ := (M.traj θ).map (fun ω ↦ ω t)
  have hK := Map.eq.BindK.of.All_EqWithDensity (M := M) θ t
  have hmap :
    (M.traj θ).map (s (t + 1)) =
      ((M.traj θ).map (fun ω ↦ ω (t + 1))).map (fun z ↦ z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply (t + 1))]; rfl
  have hsa :
    (M.traj θ).map (fun ω ↦ (s t ω, a t ω)) = μ.map (fun z ↦ z.2) := by
    rw [Measure.map_map (measurable_snd.fst.prodMk measurable_snd.snd)
      (measurable_pi_apply t)]
    rfl
  have hsk :
    (M.stageK θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) =
      Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id := by
    unfold Model.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ
        (M.kernel θ ⊗ₖ M.rewardK)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod _ _
  rw [hmap, hK, Model.K, ← Measure.comp_assoc,
    Measure.map_comp _ _ (by fun_prop), hsk,
    Measure.deterministic_comp_eq_map, Measure.map_id, hsa,
    comp_comap_eq_comp_map]

private lemma integral_Wkd_map_s
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t k : ℕ) :
  ∫ y, M.Wkd θ k y ∂((M.traj θ).map (s t)) =
    ∫ x, M.Wkd θ (t + k) x ∂(M.init : Measure _) := by
  have hπ : ∀ θ', Measurable (fun z : 𝒮 × 𝒜 => M.π[θ'] z.1 z.2) :=
    fun θ' => hStoch.measurable_π θ'
  induction t generalizing k with
  | zero =>
    rw [map_s0_eq_init h₀, zero_add]
  | succ t ih =>
    have hmeas : Measurable (M.Wkd θ k) :=
      Measurable_Wkd.of.All_Measurable_Prob hπ θ k
    have hbd : ∀ y, ‖M.Wkd θ k y‖ ≤ |M.R| := fun y =>
      NormWkd.le.Abs_R (M := M) θ k y
    have hlaw := map_s_succ (M := M) h₀ θ t
    have hInt : Integrable (M.Wkd θ k)
      (M.transK ∘ₘ (M.traj θ).map (fun ω ↦ (s t ω, a t ω))) := by
      rw [← hlaw]
      exact Integrable.of_bound hmeas.aestronglyMeasurable _
        (Filter.Eventually.of_forall hbd)
    have hφ : StronglyMeasurable
      (Function.uncurry fun (sₜ : 𝒮) (aₜ : 𝒜) =>
        ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, aₜ))) :=
      (StronglyMeasurable.integral_kernel_prod_right'
        (κ := M.transK)
        (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.Wkd θ k z.2)
        (hmeas.stronglyMeasurable.comp_measurable measurable_snd)).measurable.stronglyMeasurable
    have hC : ∀ x u, ‖∫ y, M.Wkd θ k y ∂(M.trans (x, u))‖ ≤ |M.R| :=
      fun x u => by
        simpa using norm_integral_le_of_norm_le_const
          (μ := M.trans (x, u)) (Filter.Eventually.of_forall hbd)
    have hsa : Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s t ω, a t ω) :=
      (Random.Measurable.of.All_Eq.snd.fst h₀ t).prodMk
        (Random.Measurable.of.All_Eq.snd.snd h₀ t)
    have hpath :
      ∫ ω, ∫ y, M.Wkd θ k y ∂(M.trans (s t ω, a t ω)) ∂(M.traj θ) =
        ∫ p : 𝒮 × 𝒜, ∫ y, M.Wkd θ k y ∂(M.trans p)
          ∂((M.traj θ).map (fun ω ↦ (s t ω, a t ω))) :=
      (integral_map (μ := M.traj θ) hsa.aemeasurable
        (f := fun p : 𝒮 × 𝒜 => ∫ y, M.Wkd θ k y ∂(M.trans p))
        (by convert hφ.aestronglyMeasurable; simp [Function.uncurry])).symm
    have hdecomp :=
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        (M := M) (φ := fun x u => ∫ y, M.Wkd θ k y ∂(M.trans (x, u)))
        (C := |M.R|) h₀ hφ hC θ t
    have hW : ∀ sₜ, ∫ aₜ, M.π[θ] sₜ aₜ •
      ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, aₜ)) ∂ReferenceMeasure.measure =
        M.Wkd θ (k + 1) sₜ := by
      intro sₜ
      simp only [Model.Wkd, smul_eq_mul]
    calc
      _ = ∫ p : 𝒮 × 𝒜, ∫ y, M.Wkd θ k y ∂(M.trans p)
        ∂((M.traj θ).map (fun ω ↦ (s t ω, a t ω))) := by
        rw [hlaw, Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
        simp [Model.transK]
      _ = ∫ ω, ∫ y, M.Wkd θ k y ∂(M.trans (s t ω, a t ω)) ∂(M.traj θ) :=
        hpath.symm
      _ = ∫ sₜ, (∫ aₜ, M.π[θ] sₜ aₜ •
        ∫ y, M.Wkd θ k y ∂(M.trans (sₜ, aₜ)) ∂ReferenceMeasure.measure)
        ∂((M.traj θ).map (s t)) := hdecomp
      _ = ∫ x, M.Wkd θ (k + 1) x ∂((M.traj θ).map (s t)) :=
        integral_congr_ae (Filter.Eventually.of_forall hW)
      _ = ∫ x, M.Wkd θ (t + (k + 1)) x ∂(M.init : Measure _) := ih (k + 1)
      _ = ∫ x, M.Wkd θ (t + 1 + k) x ∂(M.init : Measure _) := by
        congr 1; ext x; rw [show t + 1 + k = t + (k + 1) by omega]

/--
Expected stage reward under the continuous-action trajectory model equals the
`init`-average of the closed-form `Wkd`:
`∫ r[t] ∂(M.traj θ) = ∫ x, Wkd θ t x ∂env.init`.
Continuous-action counterpart of `Random.Integral_R.eq.Sum_MulRealWRc`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, r t ω ∂(M.traj θ) = ∫ x, M.Wkd θ t x ∂(M.init : Measure _) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₀ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  have hclip := MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₀ θ t
  have hR :
    ∫ ω, r t ω ∂(M.traj θ) =
      ∫ ω, clip (ω t).1 (-M.R) M.R ∂(M.traj θ) :=
    integral_congr_ae hclip
  have hf : StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 =>
      clip z.1 (-M.R) M.R := by
    unfold clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hCb : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.R) M.R‖ ≤ |M.R| :=
    fun z => NormClip.le.Abs_R _ _
  have hmap := Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₀ θ t
  have hInt :
    Integrable (fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.R) M.R)
      (M.stageK θ ∘ₘ (M.traj θ).map (s t)) :=
    Integrable.of_bound hf.aestronglyMeasurable _
      (Filter.Eventually.of_forall hCb)
  have hstage :
    ∫ ω, clip (ω t).1 (-M.R) M.R ∂(M.traj θ) =
      ∫ y, ∫ z, clip z.1 (-M.R) M.R ∂(M.stageK θ y)
        ∂((M.traj θ).map (s t)) := by
    have e := integral_map (μ := M.traj θ) (measurable_pi_apply t).aemeasurable
      (f := fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.R) M.R)
      hf.aestronglyMeasurable
    refine e.symm.trans ?_
    rw [hmap, Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
  have hW0 : ∀ y,
      ∫ z, clip z.1 (-M.R) M.R ∂(M.stageK θ y) = M.Wkd θ 0 y := by
    intro y
    have e :=
      Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hCb θ y
    refine e.trans ?_
    simp only [Model.Wkd, Model.rkd, smul_eq_mul]
  refine hR.trans (hstage.trans ?_)
  simp_rw [hW0]
  exact (integral_Wkd_map_s (M := M) h₀ θ t 0).trans (by rw [add_zero])


-- created on 2026-10-20
-- updated on 2026-11-16
