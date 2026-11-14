import Theorem.Probability.CondExpectation
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Kernel


attribute [local instance] Classical.propDecidable

private lemma stronglyMeasurable_indClip
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (x : 𝒮)
  (u : 𝒜) :
-- imply
  StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 =>
    (if z.2 = (x, u) then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R := by
-- proof
  have hclip : Measurable fun z : ℝ × 𝒮 × 𝒜 => clip z.1 (-M.env.R) M.env.R := by
    unfold clip
    apply (measurable_fst.max measurable_const).min measurable_const
  have hind : Measurable fun z : ℝ × 𝒮 × 𝒜 =>
    if z.2 = (x, u) then (1 : ℝ) else 0 :=
    Measurable.ite (measurable_snd (measurableSet_singleton (x, u)))
      measurable_const measurable_const
  apply (hind.mul hclip).stronglyMeasurable

private lemma leNorm_indClip
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (x : 𝒮)
  (u : 𝒜)
  (z : ℝ × 𝒮 × 𝒜) :
-- imply
  ‖(if z.2 = (x, u) then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R‖ ≤
    |M.env.R| := by
-- proof
  have hclip : ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    NormClip.le.Abs_R M.env.R z.1
  if h : z.2 = (x, u) then
    simpa [h] using hclip
  else
    simp [h]

private lemma integral_stageK_indClip
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (y x : 𝒮)
  (u : 𝒜) :
-- imply
  ∫ z,
    (if z.2 = (x, u) then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R
    ∂(M.stageK θ y) =
    (if y = x then (1 : ℝ) else 0) *
      (∫ v, M.policy.prob θ y v * (if v = u then (1 : ℝ) else 0)
        ∂ReferenceMeasure.measure) *
      M.rkd y u := by
-- proof
  have hf := stronglyMeasurable_indClip (M := M) x u
  have hC := leNorm_indClip (M := M) x u
  have e :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M)
      (f := fun z : ℝ × 𝒮 × 𝒜 =>
        (if z.2 = (x, u) then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R)
      (C := |M.env.R|) hf hC θ y
  refine e.trans ?_
  have hpt : ∀ v,
    ∫ ρ,
      (if ((ρ, y, v) : ℝ × 𝒮 × 𝒜).2 = (x, u) then (1 : ℝ) else 0) *
        clip ρ (-M.env.R) M.env.R ∂(M.env.reward (y, v)) =
      (if y = x ∧ v = u then (1 : ℝ) else 0) * M.rkd y v := by
    intro v
    if hy : y = x then
      if hv : v = u then
        simp [hy, hv, DensityModel.rkd]
      else
        simp [hv]
    else
      simp [hy]
  simp_rw [hpt, smul_eq_mul]
  if hy : y = x then
    simp only [hy, ↓reduceIte, true_and, one_mul]
    have hcong :
      (fun v =>
        M.policy.prob θ x v * ((if v = u then (1 : ℝ) else 0) * M.rkd x v)) =ᵐ[ReferenceMeasure.measure]
        fun v =>
          M.policy.prob θ x v * (if v = u then (1 : ℝ) else 0) * M.rkd x u := by
      apply Filter.Eventually.of_forall
      intro v
      if hv : v = u then
        simp [hv]
      else
        simp [hv]
    rw [integral_congr_ae hcong, integral_mul_const]
  else
    simp [hy]

private lemma integral_stageK_ind
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (y x : 𝒮)
  (u : 𝒜) :
-- imply
  ∫ z, (if z.2 = (x, u) then (1 : ℝ) else 0) ∂(M.stageK θ y) =
    (if y = x then (1 : ℝ) else 0) *
      (∫ v, M.policy.prob θ y v * (if v = u then (1 : ℝ) else 0)
        ∂ReferenceMeasure.measure) := by
-- proof
  have := M.env.reward_markov
  have hf : StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 =>
    (if z.2 = (x, u) then (1 : ℝ) else 0) := by
    apply (Measurable.ite (measurable_snd (measurableSet_singleton (x, u)))
        measurable_const measurable_const).stronglyMeasurable
  have hC : ∀ z : ℝ × 𝒮 × 𝒜,
    ‖(if z.2 = (x, u) then (1 : ℝ) else 0)‖ ≤ (1 : ℝ) := by
    intro z
    if h : z.2 = (x, u) then
      simp [h]
    else
      simp [h]
  have e :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) (f := fun z : ℝ × 𝒮 × 𝒜 => (if z.2 = (x, u) then (1 : ℝ) else 0))
      (C := (1 : ℝ)) hf hC θ y
  refine e.trans ?_
  have hpt : ∀ v,
    ∫ ρ, (if ((ρ, y, v) : ℝ × 𝒮 × 𝒜).2 = (x, u) then (1 : ℝ) else 0)
      ∂(M.env.reward (y, v)) =
      if y = x ∧ v = u then (1 : ℝ) else 0 := by
    intro v
    if hy : y = x then
      if hv : v = u then
        simp [hy, hv]
      else
        simp [hv]
    else
      simp [hy]
  simp_rw [hpt, smul_eq_mul]
  if hy : y = x then
    simp [hy]
  else
    simp [hy]

/--
On a joint atom of positive mass (`ℙ(s[t] = s_t ∧ a[t] = a_t) ≠ 0`):
`rkd s_t a_t = 𝔼[r[t] | s[t] = s_t, a[t] = a_t]`.
`rkd` integrates the reward clamped to `[-R, R]`; this agrees with the raw
stage reward because `r[t] =ᵐ clip r[t] (-R) R`
([r =ᵐ clip](?module=Random.MEq_Clip.of.All_Eq.All_EqWithDensity)).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {s_t : 𝒮}
  {a_t : 𝒜}
-- given
  (h₀ : DensityModel.IsPolicyTrajectory M r s a)
  (hP : (M θ).real ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}) ≠ 0) :
-- imply
  M.rkd s_t a_t = 𝔼[r : M θ](r t | s t = s_t ∧ a t = a_t) := by
-- proof
  have := M.env.reward_markov
  have hr : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 ↦ fun k ↦ r k ω) := by
    have : (fun ω k ↦ r k ω) = fun ω k ↦ (ω k).1 := by
      funext ω k
      apply Eq.symm
      apply congrArg Prod.fst (congrFun (h₀.stage_eq k) ω)
    rw [this]
    apply Measurable.of_eval
    intro k
    apply measurable_fst.comp
    apply measurable_pi_apply
  have hs : Measurable (s t) := h₀.measurable_s t
  have ha : Measurable (a t) := h₀.measurable_a t
  have hsa : Measurable fun ω => (s t ω, a t ω) := hs.prodMk ha
  have hB : MeasurableSet ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}) :=
    hsa (measurableSet_singleton _)
  have hpos : (M θ).map (fun ω => (s t ω, a t ω)) {(s_t, a_t)} ≠ 0 := by
    rw [Measure.map_apply hsa (measurableSet_singleton _)]
    intro hz
    apply hP
    simp [Measure.real, hz]
  have hf : Measurable fun integ : ℕ → ℝ => integ t := measurable_pi_apply t
  have hstage : ∀ t, (· t) = (r t, s t, a t) := h₀.stage_eq
  have hclip := MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) hstage θ t
  have hmap := Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) hstage θ t
  set fClip : ℝ × 𝒮 × 𝒜 → ℝ := fun z =>
    (if z.2 = (s_t, a_t) then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R
  set fInd : ℝ × 𝒮 × 𝒜 → ℝ := fun z =>
    if z.2 = (s_t, a_t) then (1 : ℝ) else 0
  have hfS := stronglyMeasurable_indClip (M := M) s_t a_t
  have hC := leNorm_indClip (M := M) s_t a_t
  have hInt :
    Integrable fClip (M.stageK θ ∘ₘ (M θ).map (s t)) :=
    Integrable.of_bound hfS.aestronglyMeasurable _ (Filter.Eventually.of_forall hC)
  have hind :
    ∫ ω, fClip (ω t) ∂(M θ) =
      ∫ y, ∫ z, fClip z ∂(M.stageK θ y) ∂((M θ).map (s t)) := by
    have e :=
      integral_map (μ := M θ) (measurable_pi_apply t).aemeasurable
        (f := fClip) hfS.aestronglyMeasurable
    refine e.symm.trans ?_
    rw [hmap, Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
  have hI : ∀ y,
    ∫ z, fClip z ∂(M.stageK θ y) =
      (if y = s_t then (1 : ℝ) else 0) *
        (∫ v, M.policy.prob θ y v * (if v = a_t then (1 : ℝ) else 0)
          ∂ReferenceMeasure.measure) *
        M.rkd y a_t :=
    fun y => integral_stageK_indClip (M := M) θ y s_t a_t
  have hIndS : StronglyMeasurable fInd := by
    apply (Measurable.ite (measurable_snd (measurableSet_singleton (s_t, a_t)))
        measurable_const measurable_const).stronglyMeasurable
  have hC1 : ∀ z, ‖fInd z‖ ≤ (1 : ℝ) := by
    intro z
    if h : z.2 = (s_t, a_t) then
      simp [fInd, h]
    else
      simp [fInd, h]
  have hInt1 :
    Integrable fInd (M.stageK θ ∘ₘ (M θ).map (s t)) :=
    Integrable.of_bound hIndS.aestronglyMeasurable _ (Filter.Eventually.of_forall hC1)
  have hind1 :
    ∫ ω, fInd (ω t) ∂(M θ) =
      ∫ y, ∫ z, fInd z ∂(M.stageK θ y) ∂((M θ).map (s t)) := by
    have e :=
      integral_map (μ := M θ) (measurable_pi_apply t).aemeasurable
        (f := fInd) hIndS.aestronglyMeasurable
    refine e.symm.trans ?_
    rw [hmap, Integral.eq.Integral_Integral.of.Integrable_Bind hInt1]
  have hmass :
    ∫ ω, fInd (ω t) ∂(M θ) =
      (M θ).real ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}) := by
    have hfun : (fun ω => fInd (ω t)) =
      ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      have hsaω : (s t ω, a t ω) = (ω t).2 :=
        (congrArg Prod.snd (congrFun (hstage t) ω)).symm
      if h : (ω t).2 = (s_t, a_t) then
        simp [fInd, h, hsaω, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
      else
        simp [fInd, h, hsaω, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    rw [hfun, integral_indicator hB, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  have hprod :
    ∫ ω, fClip (ω t) ∂(M θ) =
      (M θ).real ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}) * M.rkd s_t a_t := by
    rw [hind]
    simp_rw [hI]
    have hfactor :
      ∫ y,
        (if y = s_t then (1 : ℝ) else 0) *
          (∫ v, M.policy.prob θ y v * (if v = a_t then (1 : ℝ) else 0)
            ∂ReferenceMeasure.measure) *
          M.rkd y a_t ∂((M θ).map (s t)) =
        (∫ y,
          (if y = s_t then (1 : ℝ) else 0) *
            (∫ v, M.policy.prob θ y v * (if v = a_t then (1 : ℝ) else 0)
              ∂ReferenceMeasure.measure) ∂((M θ).map (s t))) *
          M.rkd s_t a_t := by
      have hcong :=
        integral_congr_ae (μ := (M θ).map (s t))
          (Filter.Eventually.of_forall fun y =>
            show
              (if y = s_t then (1 : ℝ) else 0) *
                (∫ v, M.policy.prob θ y v * (if v = a_t then (1 : ℝ) else 0)
                  ∂ReferenceMeasure.measure) *
                M.rkd y a_t =
              (if y = s_t then (1 : ℝ) else 0) *
                (∫ v, M.policy.prob θ y v * (if v = a_t then (1 : ℝ) else 0)
                  ∂ReferenceMeasure.measure) *
                M.rkd s_t a_t by
              if hy : y = s_t then
                simp [hy]
              else
                simp [hy])
      refine hcong.trans ?_
      rw [← integral_mul_const]
    refine hfactor.trans ?_
    have : ∫ y,
      (if y = s_t then (1 : ℝ) else 0) *
        (∫ v, M.policy.prob θ y v * (if v = a_t then (1 : ℝ) else 0)
          ∂ReferenceMeasure.measure) ∂((M θ).map (s t)) =
      (M θ).real ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}) := by
      have hI1 : ∀ y,
        ∫ z, fInd z ∂(M.stageK θ y) =
          (if y = s_t then (1 : ℝ) else 0) *
            (∫ v, M.policy.prob θ y v * (if v = a_t then (1 : ℝ) else 0)
              ∂ReferenceMeasure.measure) :=
        fun y => integral_stageK_ind (M := M) θ y s_t a_t
      simp_rw [← hI1]
      rw [← hind1, hmass]
    rw [this]
  have hcond :
    ∫ ω, r t ω ∂(M θ)[|(fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}] =
      M.rkd s_t a_t := by
    have hnorm :
      ∫ ω, r t ω ∂(M θ)[|(fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}] =
        ((M θ).real ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}))⁻¹ *
          ∫ ω,
            ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}).indicator
                (fun _ => (1 : ℝ)) ω * r t ω ∂(M θ) := by
      rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hB,
        ENNReal.toReal_inv, ← measureReal_def, smul_eq_mul]
      congr 1
      congr 1
      funext ω
      if h : ω ∈ ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}) then
        simp [h]
      else
        simp [h]
    refine hnorm.trans ?_
    have hswap :
      ∫ ω,
        ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}).indicator
            (fun _ => (1 : ℝ)) ω * r t ω ∂(M θ) =
        ∫ ω, fClip (ω t) ∂(M θ) := by
      have hae :
        (fun ω =>
          ((fun ω => (s t ω, a t ω)) ⁻¹' {(s_t, a_t)}).indicator
              (fun _ => (1 : ℝ)) ω * r t ω) =ᵐ[M θ]
          fun ω => fClip (ω t) := by
        filter_upwards [hclip] with ω hω
        have hsaω : (s t ω, a t ω) = (ω t).2 :=
          (congrArg Prod.snd (congrFun (hstage t) ω)).symm
        have hrω : r t ω = (ω t).1 :=
          (congrArg Prod.fst (congrFun (hstage t) ω)).symm
        if h : (ω t).2 = (s_t, a_t) then
          simp [fClip, h, hsaω, hrω, Set.indicator, Set.mem_preimage,
            Set.mem_singleton_iff]
          apply hrω.symm.trans hω
        else
          simp [fClip, h, hsaω, Set.indicator, Set.mem_preimage,
            Set.mem_singleton_iff]
      apply integral_congr_ae hae
    rw [hswap, hprod]
    have hne := hP
    field_simp [hne]
  apply Eq.symm
  apply (Expectation.condEval_eq_integral hr hsa hf hpos).trans
  apply hcond


-- created on 2026-11-13
