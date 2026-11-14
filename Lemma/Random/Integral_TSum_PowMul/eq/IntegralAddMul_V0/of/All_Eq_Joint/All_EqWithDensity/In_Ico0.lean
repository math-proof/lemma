import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.All_EqWithDensity.In_Ico
import Lemma.Random.V.eq.V0.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Wkd.eq.Integral_Kf.of.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Theorem.Probability.CondExpectation
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Kernel Finset Filter
set_option maxHeartbeats 400000


attribute [local instance] Classical.propDecidable

/-- The stage kernel `stageK θ y` is supported on the state `y`. -/
private lemma ae_state_stageK
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (y : 𝒮) :
-- imply
  ∀ᵐ z ∂(M.stageK θ y), z.2.1 = y := by
-- proof
  have := M.env.reward_markov
  have hsk :
    (M.stageK θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) =
      Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id := by
    unfold DensityModel.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ
        (M.policy.kernel θ ⊗ₖ M.env.reward)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod _ _
  rw [ae_iff]
  have hset : {z : ℝ × 𝒮 × 𝒜 | ¬z.2.1 = y} = (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) ⁻¹' ({y}ᶜ) := by
    ext z; simp
  rw [hset, ← Measure.map_apply (μ := M.stageK θ y) measurable_snd.fst
    (measurableSet_singleton y).compl, ← Kernel.map_apply (M.stageK θ)
    (f := fun z : ℝ × 𝒮 × 𝒜 => z.2.1) (hf := measurable_snd.fst), hsk,
    Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton y).compl]
  simp

/-- The stage kernel `stageK θ y` is supported on the state `y`. -/
private lemma integral_V0_stageK
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
-- given
  (θ : Θ)
  (y : 𝒮) :
-- imply
  ∫ z, M.V0 θ γ z.2.1 ∂(M.stageK θ y) = M.V0 θ γ y := by
-- proof
  have hV0 : Measurable (M.V0 θ γ) :=
    Measurable_Vkd.of.All_Measurable_Prob (M := M)
      (fun θ => M.policy.measurable_prob θ) θ γ
  have := M.env.reward_markov
  have hsk :
    (M.stageK θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) =
      Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id := by
    unfold DensityModel.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ
        (M.policy.kernel θ ⊗ₖ M.env.reward)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod _ _
  rw [← integral_map measurable_snd.fst.aemeasurable hV0.aestronglyMeasurable]
  rw [← Kernel.map_apply (M.stageK θ) (f := fun z : ℝ × 𝒮 × 𝒜 => z.2.1)
    (hf := measurable_snd.fst)]
  rw [hsk, Kernel.deterministic_apply]
  exact integral_dirac' _ y hV0.stronglyMeasurable

/-- Integrating a function of the next state against `K θ w` is integrating it against the transition. -/
private lemma integral_V0_K
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {h : γ ∈ Set.Ico 0 1}
-- given
  (θ : Θ)
  (w : ℝ × 𝒮 × 𝒜) :
-- imply
  ∫ z, M.V0 θ γ z.2.1 ∂(M.K θ w) =
    ∫ y, M.V0 θ γ y ∂(M.env.trans w.2) := by
-- proof
  have := M.env.trans_markov
  have := M.env.reward_markov
  have hV0 : Measurable (M.V0 θ γ) :=
    Measurable_Vkd.of.All_Measurable_Prob (M := M)
      (fun θ => M.policy.measurable_prob θ) θ γ
  have hg : StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 => M.V0 θ γ z.2.1 :=
    (hV0.comp measurable_snd.fst).stronglyMeasurable
  have hK : M.K θ w = M.stageK θ ∘ₘ M.env.trans w.2 := by
    rw [DensityModel.K, Kernel.comp_apply, Kernel.comap_apply]
  rw [hK]
  have hV0b : ∀ y, ‖M.V0 θ γ y‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h θ y
  have hint : Integrable (fun z : ℝ × 𝒮 × 𝒜 => M.V0 θ γ z.2.1)
      (M.stageK θ ∘ₘ M.env.trans w.2) :=
    Integrable.of_bound hg.aestronglyMeasurable ((1 - γ)⁻¹ * |M.env.R|)
      (Filter.Eventually.of_forall fun z => hV0b z.2.1)
  have := Integral.eq.Integral_Integral.of.Integrable_Bind (κ := M.stageK θ)
    (μ := M.env.trans w.2) hint
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact integral_V0_stageK (M := M) θ y

/--
Bellman identity for the state-value, in integral form, under a continuous-action
density model.

The left-hand side is the unfolded conditional-integral series for `V`.
The right-hand side uses the kernel state-value `V0`, which is defined on every state:
on a continuous state space the inner observational atom `s(t+1)⁻¹{s(t+1) ω}` is typically
null, so the discrete inner conditional would vanish while `V0` does not.
When the atom `B = {s[t] = x}` is null, both sides are zero.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : 𝒮) :
-- imply
  ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}] =
    ∫ ω, (γ * M.V0 θ γ (s (t + 1) ω) + r t ω)
      ∂(M θ)[|s t ⁻¹' {x}] := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  set B : Set (ℕ → ℝ × 𝒮 × 𝒜) := s t ⁻¹' {x}
  have hBm : MeasurableSet B :=
    (measurable_pi_apply t).snd.fst (measurableSet_singleton x)
  if hB : (M θ) B = 0 then
    simp [cond_eq_zero_of_meas_eq_zero hB]
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    have := M.env.reward_markov
    have := M.env.trans_markov
    have hQA : (M θ).real B ≠ 0 := by
      intro hz
      exact hB ((ENNReal.toReal_eq_zero_iff _).1 hz |>.resolve_right
        (measure_ne_top (M θ) B))
    have hLHS :=
      Integral_G.eq.TSum_MulPowIntegral_R_Add.of.All_EqWithDensity.In_Ico
        (M := M) h₀ h₁ θ B t
    rw [← hLHS]
    have hpR : Measurable (fun ω k ↦ r k ω) :=
      Measurable.of_eval fun k => measurable_fst.comp (measurable_pi_apply k)
    have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) := by
      unfold Dot.dot Function.getSliceFrom
      refine Measurable.tsum fun k => ?_
      have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
      simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
    have hs : Measurable (s t) := (measurable_pi_apply t).snd.fst
    have hmap : (M θ).map (s t) {x} ≠ 0 := by
      rw [Measure.map_apply hs (measurableSet_singleton x)]
      exact fun hz => hQA (by simp [Measure.real, B, s, hz])
    have hVobs : ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω ∂(M θ)[|B] = M.V θ γ t x := by
      unfold DensityModel.V
      simp only [Expectation.asRV_process]
      rw [Expectation.condEval_eq_integral hpR hs hfG hmap]
      rfl
    have hVV0 : M.V θ γ t x = M.V0 θ γ x :=
      V.eq.V0.of.Ne0Real_Preimage.In_Ico (M := M) h₀ (by
        simpa [B, s, Measure.real] using hQA)
    rw [hVobs, hVV0,
      Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob (M := M)
        (fun θ => M.policy.measurable_prob θ) h₀ θ x]
    have hV0m : Measurable (M.V0 θ γ) :=
      Measurable_Vkd.of.All_Measurable_Prob (M := M)
        (fun θ => M.policy.measurable_prob θ) θ γ
    have hV0b : ∀ y, ‖M.V0 θ γ y‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
      fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y
    have hr_int : Integrable (fun ω => r t ω) (M θ)[|B] :=
      Integrable.of_bound
        (measurable_fst.comp (measurable_pi_apply t)).aestronglyMeasurable
        |M.env.R|
        (cond_absolutelyContinuous.ae_le
          ((MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₁ θ t).mono
            fun ω hω => by
              rw [hω]
              exact NormClip.le.Abs_R M.env.R (ω t).1))
    have hV_int : Integrable (fun ω => M.V0 θ γ (s (t + 1) ω)) (M θ)[|B] :=
      Integrable.of_bound
        (hV0m.comp (measurable_snd.fst.comp (measurable_pi_apply (t + 1)))).aestronglyMeasurable
        ((1 - γ)⁻¹ * |M.env.R|)
        (Filter.Eventually.of_forall fun ω => hV0b (s (t + 1) ω))
    have hsplit :
      ∫ ω, (γ * M.V0 θ γ (s (t + 1) ω) + r t ω) ∂(M θ)[|B] =
        γ * (∫ ω, M.V0 θ γ (s (t + 1) ω) ∂(M θ)[|B]) +
          (∫ ω, r t ω ∂(M θ)[|B]) := by
      rw [integral_add (hV_int.const_mul γ) hr_int, integral_const_mul]
    rw [hsplit]
    have hcond : ∀ {f : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ},
        ∫ ω, f ω ∂(M θ)[|B] =
          ((M θ).real B)⁻¹ * ∫ ω, B.indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) ω * f ω ∂(M θ) := by
      intro f
      rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hBm,
        ENNReal.toReal_inv, ← measureReal_def, smul_eq_mul]
      congr 1
      congr 1
      funext ω
      by_cases hω : ω ∈ B <;> simp [hω]
    have hι : ∀ ω, B.indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) ω =
        if (ω t).2.1 = x then (1 : ℝ) else 0 := by
      intro ω
      if hω : (ω t).2.1 = x then
        simp [B, s, hω, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
      else
        simp [B, s, hω, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    have hclip : StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 =>
        clip z.1 (-M.env.R) M.env.R :=
      ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
    have hclipC : ∀ z : ℝ × 𝒮 × 𝒜, ‖clip z.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
      fun z => NormClip.le.Abs_R M.env.R z.1
    -- `∫ r[t] ∂cond(B) = ∫ π rkd = Wkd θ 0 x`
    have hr : ∫ ω, r t ω ∂(M θ)[|B] =
        ∫ u, M.policy.prob θ x u * M.rkd x u ∂μ.measure := by
      rw [hcond]
      simp_rw [hι]
      have hcr : ∫ ω, (if (ω t).2.1 = x then (1 : ℝ) else 0) * r t ω ∂(M θ) =
          ∫ ω, (if (ω t).2.1 = x then (1 : ℝ) else 0) *
            clip (ω t).1 (-M.env.R) M.env.R ∂(M θ) := by
        refine integral_congr_ae ?_
        filter_upwards [MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₁ θ t] with ω hω
        simp [hω]
      rw [hcr]
      have hmap_t :=
        Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ t
      have hfι : StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 =>
          (if z.2.1 = x then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R :=
        ((Measurable.ite (measurable_snd.fst (measurableSet_singleton x))
          measurable_const measurable_const).mul
          ((measurable_fst.max measurable_const).min measurable_const)).stronglyMeasurable
      have hmap_int :=
        integral_map (μ := M θ) (measurable_pi_apply t).aemeasurable
          (f := fun z : ℝ × 𝒮 × 𝒜 =>
            (if z.2.1 = x then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R)
          hfι.aestronglyMeasurable
      rw [hmap_int.symm, hmap_t]
      have hCι : ∀ z : ℝ × 𝒮 × 𝒜,
          ‖(if z.2.1 = x then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R‖ ≤
            |M.env.R| := by
        intro z
        have h := hclipC z
        by_cases hz : z.2.1 = x
        · simpa [hz, Real.norm_eq_abs] using h
        · simp [hz]
      have hint : Integrable
          (fun z : ℝ × 𝒮 × 𝒜 =>
            (if z.2.1 = x then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R)
          (M.stageK θ ∘ₘ (M θ).map (s t)) :=
        Integrable.of_bound hfι.aestronglyMeasurable _ (Filter.Eventually.of_forall hCι)
      rw [Integral.eq.Integral_Integral.of.Integrable_Bind hint]
      have hy : ∀ y,
          ∫ z, (if z.2.1 = x then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R
            ∂(M.stageK θ y) =
            (if y = x then (1 : ℝ) else 0) * M.Wkd θ 0 y := by
        intro y
        have hae := ae_state_stageK (M := M) θ y
        have hcongr :
            ∫ z, (if z.2.1 = x then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R
              ∂(M.stageK θ y) =
            ∫ z, (if y = x then (1 : ℝ) else 0) * clip z.1 (-M.env.R) M.env.R
              ∂(M.stageK θ y) := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with z hz
          simp [hz]
        rw [hcongr, integral_const_mul, Wkd.eq.Integral_Kf.of.All_EqWithDensity (M := M) θ 0 y]
        simp [DensityModel.Kf]
      simp_rw [hy]
      have hite : (fun y : 𝒮 => (if y = x then (1 : ℝ) else 0) * M.Wkd θ 0 y) =
          ({x} : Set 𝒮).indicator (fun _ => M.Wkd θ 0 x) := by
        funext y
        by_cases hy : y = x <;> simp [hy, Set.indicator]
      rw [hite, integral_indicator (measurableSet_singleton x),
        MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
      have hmeas : (M θ).map (s t) {x} = (M θ) B :=
        Measure.map_apply hs (measurableSet_singleton x)
      have : ((M θ).map (s t)).real {x} = (M θ).real B := by
        simp [Measure.real, hmeas]
      rw [this]
      field_simp [hQA]
      rfl
    -- `∫ V0(s[t+1]) ∂cond(B) = ∫ π ∫ V0 ∂trans`
    have hV :
      ∫ ω, M.V0 θ γ (s (t + 1) ω) ∂(M θ)[|B] =
        ∫ u, M.policy.prob θ x u * ∫ y, M.V0 θ γ y ∂(M.env.trans (x, u))
          ∂μ.measure := by
      rw [hcond]
      simp_rw [hι]
      let G : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → ℝ :=
        fun hist => if (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = x then 1 else 0
      have hG : StronglyMeasurable G := by
        have hset : MeasurableSet {hist : Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜 |
            (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = x} :=
          (measurable_pi_apply _).snd.fst (measurableSet_singleton x)
        have hιG : StronglyMeasurable (fun hist : Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜 =>
            if hist ∈ {hist | (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = x} then (1 : ℝ) else 0) :=
          (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
        have hιG' : G = fun hist =>
            if hist ∈ {hist : Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜 |
              (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = x} then (1 : ℝ) else 0 := by
          funext hist
          simp [G]
        exact hιG'.symm ▸ hιG
      have hCG : ∀ hist, ‖G hist‖ ≤ 1 := by
        intro hist
        if hh : (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = x then
          simp [G, hh]
        else
          simp [G, hh]
      have hg : StronglyMeasurable fun z : ℝ × 𝒮 × 𝒜 => M.V0 θ γ z.2.1 :=
        (hV0m.comp measurable_snd.fst).stronglyMeasurable
      have hgC : ∀ z : ℝ × 𝒮 × 𝒜, ‖M.V0 θ γ z.2.1‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
        fun z => hV0b z.2.1
      have hGapp : ∀ ω : ℕ → ℝ × 𝒮 × 𝒜,
          G (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω) =
            if (ω t).2.1 = x then (1 : ℝ) else 0 := by
        intro ω
        unfold G
        refine ite_congr ?_ (fun _ => rfl) (fun _ => rfl)
        simp [Preorder.frestrictLe_apply]
      have hmark :=
        Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hG hCG hg hgC θ (n := t)
      have hωk : (fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
          (if (ω t).2.1 = x then (1 : ℝ) else 0) *
            M.V0 θ γ (s (t + 1) ω)) =
          fun ω =>
            G (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω) *
              (fun z : ℝ × 𝒮 × 𝒜 => M.V0 θ γ z.2.1) (ω (t + 1)) := by
        funext ω
        simp [hGapp, s]
      rw [hωk, hmark]
      have happ : (fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
          G (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω) *
            (∫ z, M.V0 θ γ z.2.1 ∂(M.K θ (ω t)))) =
          fun ω => (if (ω t).2.1 = x then (1 : ℝ) else 0) *
            (∫ z, M.V0 θ γ z.2.1 ∂(M.K θ (ω t))) := by
        funext ω; simp [hGapp]
      rw [happ]
      have hKpt : ∀ ω : ℕ → ℝ × 𝒮 × 𝒜,
          (if (ω t).2.1 = x then (1 : ℝ) else 0) *
              (∫ z, M.V0 θ γ z.2.1 ∂(M.K θ (ω t))) =
            (if (ω t).2.1 = x then (1 : ℝ) else 0) *
              (∫ y, M.V0 θ γ y ∂(M.env.trans (s t ω, a t ω))) := by
        intro ω
        if hω : (ω t).2.1 = x then
          rw [integral_V0_K (M := M) (h := h₀) θ (ω t)]
        else
          simp [hω]
      simp_rw [hKpt]
      let φ : 𝒮 → 𝒜 → ℝ := fun y u =>
        (if y = x then (1 : ℝ) else 0) * ∫ z, M.V0 θ γ z ∂(M.env.trans (y, u))
      have hφeq : (fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
          (if (ω t).2.1 = x then (1 : ℝ) else 0) *
            (∫ y, M.V0 θ γ y ∂(M.env.trans (s t ω, a t ω)))) =
          fun ω => φ (s t ω) (a t ω) := by
        funext ω
        simp [φ, s, a]
      rw [hφeq]
      have hφm : StronglyMeasurable (Function.uncurry φ) := by
        have hInt : Measurable fun p : 𝒮 × 𝒜 =>
            ∫ z, M.V0 θ γ z ∂(M.env.trans p) :=
          ((StronglyMeasurable.integral_kernel_prod_right'
            (κ := M.env.trans)
            (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.V0 θ γ z.2)
            (hV0m.stronglyMeasurable.comp_measurable measurable_snd)).measurable)
        have hset : MeasurableSet {p : 𝒮 × 𝒜 | p.1 = x} :=
          measurable_fst (measurableSet_singleton x)
        have : Function.uncurry φ = fun p : 𝒮 × 𝒜 =>
            (if p.1 = x then (1 : ℝ) else 0) * ∫ z, M.V0 θ γ z ∂(M.env.trans p) := rfl
        rw [this]
        exact ((Measurable.ite hset measurable_const measurable_const).mul hInt).stronglyMeasurable
      have hφC : ∀ y u, ‖φ y u‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
        intro y u
        have hbd := norm_integral_le_of_norm_le_const (μ := M.env.trans (y, u))
          (Filter.Eventually.of_forall fun z => hV0b z)
        have : 0 ≤ (1 - γ)⁻¹ * |M.env.R| :=
          mul_nonneg (inv_nonneg.2 (le_of_lt (sub_pos.2 h₀.2))) (abs_nonneg _)
        by_cases hy : y = x
        · simpa [φ, hy] using hbd
        · simp [φ, hy, this]
      have hmarg :=
        Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
          (M := M) (E := ℝ) h₁ hφm hφC θ t
      rw [hmarg]
      have hy : ∀ y,
          (∫ u, M.policy.prob θ y u • φ y u ∂μ.measure) =
            (if y = x then (1 : ℝ) else 0) *
              (∫ u, M.policy.prob θ x u *
                (∫ z, M.V0 θ γ z ∂(M.env.trans (x, u))) ∂μ.measure) := by
        intro y
        by_cases hy : y = x
        · subst hy
          simp [φ, smul_eq_mul]
        · simp [φ, hy, smul_eq_mul]
      simp_rw [hy]
      have hite : (fun y : 𝒮 =>
          (if y = x then (1 : ℝ) else 0) *
            (∫ u, M.policy.prob θ x u *
              (∫ z, M.V0 θ γ z ∂(M.env.trans (x, u))) ∂μ.measure)) =
          ({x} : Set 𝒮).indicator (fun _ =>
            ∫ u, M.policy.prob θ x u *
              (∫ z, M.V0 θ γ z ∂(M.env.trans (x, u))) ∂μ.measure) := by
        funext y
        by_cases hy : y = x <;> simp [hy, Set.indicator]
      rw [hite, integral_indicator (measurableSet_singleton x),
        MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
      have hmeas : (M θ).map (s t) {x} = (M θ) B :=
        Measure.map_apply hs (measurableSet_singleton x)
      have : ((M θ).map (s t)).real {x} = (M θ).real B := by
        simp [Measure.real, hmeas]
      rw [this]
      field_simp [hQA]
    rw [hr, hV, add_comm]


-- created on 2023-03-27
