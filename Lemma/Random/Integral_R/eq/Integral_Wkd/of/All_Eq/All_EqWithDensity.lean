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
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Kernel
set_option maxHeartbeats 400000


private lemma map_s0_eq_init
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
  (M θ).map (s 0) = M.env.init := by
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  have : (M θ).map (s 0) = ((M θ).map (fun ω ↦ ω 0)).map (fun z ↦ z.2.1) := by
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
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
  (M θ).map (s (t + 1)) =
    M.env.trans ∘ₘ (M θ).map (fun ω ↦ (s t ω, a t ω)) := by
  have := M.env.trans_markov
  have := M.env.reward_markov
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  set μ := (M θ).map (fun ω ↦ ω t)
  have hK := Map.eq.BindK.of.All_EqWithDensity (M := M) θ t
  have hmap :
    (M θ).map (s (t + 1)) =
      ((M θ).map (fun ω ↦ ω (t + 1))).map (fun z ↦ z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply (t + 1))]; rfl
  have hsa :
    (M θ).map (fun ω ↦ (s t ω, a t ω)) = μ.map (fun z ↦ z.2) := by
    rw [Measure.map_map (measurable_snd.fst.prodMk measurable_snd.snd)
      (measurable_pi_apply t)]
    rfl
  have hsk :
    (M.stageK θ).map (fun z : ℝ × S × A => z.2.1) =
      Kernel.deterministic (id : S → S) measurable_id := by
    unfold DensityModel.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ
        (M.policy.kernel θ ⊗ₖ M.env.reward)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod _ _
  rw [hmap, hK, DensityModel.K, ← Measure.comp_assoc,
    Measure.map_comp _ _ (by fun_prop), hsk,
    Measure.deterministic_comp_eq_map, Measure.map_id, hsa,
    comp_comap_eq_comp_map]

private lemma integral_Wkd_map_s
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t k : ℕ) :
  ∫ y, M.Wkd θ k y ∂((M θ).map (s t)) =
    ∫ x, M.Wkd θ (t + k) x ∂M.env.init := by
  have := M.env.init_prob
  have := M.env.trans_markov
  have hπ : ∀ θ', Measurable (fun z : S × A => M.policy.prob θ' z.1 z.2) :=
    fun θ' => M.policy.measurable_prob θ'
  induction t generalizing k with
  | zero =>
    rw [map_s0_eq_init h₀, zero_add]
  | succ t ih =>
    have hmeas : Measurable (M.Wkd θ k) :=
      Measurable_Wkd.of.All_Measurable_Prob hπ θ k
    have hbd : ∀ y, ‖M.Wkd θ k y‖ ≤ |M.env.R| := fun y =>
      NormWkd.le.Abs_R (M := M) θ k y
    have hlaw := map_s_succ (M := M) h₀ θ t
    have hInt : Integrable (M.Wkd θ k)
      (M.env.trans ∘ₘ (M θ).map (fun ω ↦ (s t ω, a t ω))) := by
      rw [← hlaw]
      exact Integrable.of_bound hmeas.aestronglyMeasurable _
        (Filter.Eventually.of_forall hbd)
    have hφ : StronglyMeasurable
      (Function.uncurry fun (x : S) (u : A) =>
        ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))) :=
      (StronglyMeasurable.integral_kernel_prod_right'
        (κ := M.env.trans)
        (f := fun z : (S × A) × S => M.Wkd θ k z.2)
        (hmeas.stronglyMeasurable.comp_measurable measurable_snd)).measurable.stronglyMeasurable
    have hC : ∀ x u, ‖∫ y, M.Wkd θ k y ∂(M.env.trans (x, u))‖ ≤ |M.env.R| :=
      fun x u => by
        simpa using norm_integral_le_of_norm_le_const
          (μ := M.env.trans (x, u)) (Filter.Eventually.of_forall hbd)
    have hsa : Measurable fun ω : ℕ → ℝ × S × A => (s t ω, a t ω) :=
      (Random.Measurable.of.All_Eq.snd.fst h₀ t).prodMk
        (Random.Measurable.of.All_Eq.snd.snd h₀ t)
    have hpath :
      ∫ ω, ∫ y, M.Wkd θ k y ∂(M.env.trans (s t ω, a t ω)) ∂(M θ) =
        ∫ p : S × A, ∫ y, M.Wkd θ k y ∂(M.env.trans p)
          ∂((M θ).map (fun ω ↦ (s t ω, a t ω))) :=
      (integral_map (μ := M θ) hsa.aemeasurable
        (f := fun p : S × A => ∫ y, M.Wkd θ k y ∂(M.env.trans p))
        hφ.aestronglyMeasurable).symm
    have hdecomp :=
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        (M := M) (φ := fun x u => ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)))
        (C := |M.env.R|) h₀ hφ hC θ t
    have hW : ∀ x, ∫ u, M.policy.prob θ x u •
      ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure =
        M.Wkd θ (k + 1) x := by
      intro x
      simp only [DensityModel.Wkd, smul_eq_mul]
    calc
      _ = ∫ p : S × A, ∫ y, M.Wkd θ k y ∂(M.env.trans p)
        ∂((M θ).map (fun ω ↦ (s t ω, a t ω))) := by
        rw [hlaw, Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
      _ = ∫ ω, ∫ y, M.Wkd θ k y ∂(M.env.trans (s t ω, a t ω)) ∂(M θ) :=
        hpath.symm
      _ = ∫ x, (∫ u, M.policy.prob θ x u •
        ∫ y, M.Wkd θ k y ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure)
        ∂((M θ).map (s t)) := hdecomp
      _ = ∫ x, M.Wkd θ (k + 1) x ∂((M θ).map (s t)) :=
        integral_congr_ae (Filter.Eventually.of_forall hW)
      _ = ∫ x, M.Wkd θ (t + (k + 1)) x ∂M.env.init := ih (k + 1)
      _ = ∫ x, M.Wkd θ (t + 1 + k) x ∂M.env.init := by
        congr 1; ext x; rw [show t + 1 + k = t + (k + 1) by omega]

/--
Expected stage reward under the continuous-action trajectory model equals the
`init`-average of the closed-form `Wkd`:
`∫ r[t] ∂(M θ) = ∫ x, Wkd θ t x ∂env.init`.
Continuous-action counterpart of `Random.Integral_R.eq.Sum_MulRealWRc`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, r t ω ∂(M θ) = ∫ x, M.Wkd θ t x ∂M.env.init := by
-- proof
  have := M.env.init_prob
  have := M.env.reward_markov
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₀ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  have hclip := MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₀ θ t
  have hR :
    ∫ ω, r t ω ∂(M θ) =
      ∫ ω, clip (ω t).1 (-M.env.R) M.env.R ∂(M θ) :=
    integral_congr_ae hclip
  have hf : StronglyMeasurable fun z : ℝ × S × A =>
      clip z.1 (-M.env.R) M.env.R := by
    unfold clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hCb : ∀ z : ℝ × S × A, ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun z => NormClip.le.Abs_R _ _
  have hmap := Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₀ θ t
  have hInt :
    Integrable (fun z : ℝ × S × A => clip z.1 (-M.env.R) M.env.R)
      (M.stageK θ ∘ₘ (M θ).map (s t)) :=
    Integrable.of_bound hf.aestronglyMeasurable _
      (Filter.Eventually.of_forall hCb)
  have hstage :
    ∫ ω, clip (ω t).1 (-M.env.R) M.env.R ∂(M θ) =
      ∫ y, ∫ z, clip z.1 (-M.env.R) M.env.R ∂(M.stageK θ y)
        ∂((M θ).map (s t)) := by
    have e := integral_map (μ := M θ) (measurable_pi_apply t).aemeasurable
      (f := fun z : ℝ × S × A => clip z.1 (-M.env.R) M.env.R)
      hf.aestronglyMeasurable
    refine e.symm.trans ?_
    rw [hmap, Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
  have hW0 : ∀ y,
      ∫ z, clip z.1 (-M.env.R) M.env.R ∂(M.stageK θ y) = M.Wkd θ 0 y := by
    intro y
    have e :=
      Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hCb θ y
    refine e.trans ?_
    simp only [DensityModel.Wkd, DensityModel.rkd, smul_eq_mul]
  refine hR.trans (hstage.trans ?_)
  simp_rw [hW0]
  exact (integral_Wkd_map_s (M := M) h₀ θ t 0).trans (by rw [add_zero])


-- created on 2026-10-20
