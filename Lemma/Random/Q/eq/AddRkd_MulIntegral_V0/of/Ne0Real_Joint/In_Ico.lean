import Lemma.Random.SubAddKfMul_KfKf.eq.Zero.of.In_Ico.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Theorem.Probability.CondExpectation
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Random.Wkd.eq.Integral_Kf.of.All_EqWithDensity
import Lemma.Random.Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Finset Kernel
set_option maxHeartbeats 800000


attribute [local instance] Classical.propDecidable


private lemma Kf_succ_eq_Wkd
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (R : ℝ)
  (θ : Θ)
  (j : ℕ)
  (z : ℝ × 𝒮 × 𝒜) :
-- imply
  M.Kf θ (fun w : ℝ × 𝒮 × 𝒜 ↦ clip w.1 (-R) R) (j + 1) z =
    ∫ y, M.Wkd R θ j y ∂(M.trans z.2) := by
-- proof
  let clipf : ℝ × 𝒮 × 𝒜 → ℝ := fun w ↦ clip w.1 (-R) R
  have hf : StronglyMeasurable clipf := by
    unfold clipf clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ w : ℝ × 𝒮 × 𝒜, ‖clipf w‖ ≤ |R| :=
    fun w => NormClip.le.Abs_R R w.1
  have hKf :=
    StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ j
  have hTW :=
    Kf.eq.Integral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ j z
  refine hTW.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact (Wkd.eq.Integral_Kf.of.All_EqWithDensity (M := M) R θ j y).symm

private lemma joint_disint
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {g : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hg : StronglyMeasurable g)
  (hC : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ)
  (t : ℕ)
  (sₜ : 𝒮)
  (aₜ : 𝒜) :
-- imply
  ∫ ω, (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) * g (ω t) ∂(M θ) =
    ((M θ).map (s t)).real {sₜ} * M.π θ sₜ aₜ *
      ReferenceMeasure.measure.real {aₜ} *
      ∫ ρ, g (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)) := by
-- proof
  let ι : ℝ × 𝒮 × 𝒜 → ℝ := fun z => if z.2.1 = sₜ ∧ z.2.2 = aₜ then 1 else 0
  have hsι : MeasurableSet {z : ℝ × 𝒮 × 𝒜 | z.2.1 = sₜ ∧ z.2.2 = aₜ} :=
    (measurable_snd.fst (measurableSet_singleton sₜ)).inter
      (measurable_snd.snd (measurableSet_singleton aₜ))
  have hι : StronglyMeasurable ι := by
    have hset : StronglyMeasurable (fun z : ℝ × 𝒮 × 𝒜 =>
        if z ∈ {z : ℝ × 𝒮 × 𝒜 | z.2.1 = sₜ ∧ z.2.2 = aₜ} then (1 : ℝ) else 0) :=
      (Measurable.ite hsι measurable_const measurable_const).stronglyMeasurable
    have hι' : ι = fun z =>
        if z ∈ {z : ℝ × 𝒮 × 𝒜 | z.2.1 = sₜ ∧ z.2.2 = aₜ} then (1 : ℝ) else 0 := by
      funext z
      simp [ι]
    exact hι'.symm ▸ hset
  have hf : StronglyMeasurable (fun z => ι z * g z) := hι.mul hg
  have hCf : ∀ z, ‖ι z * g z‖ ≤ C := by
    intro z
    if hz : z.2.1 = sₜ ∧ z.2.2 = aₜ then
      simpa [ι, hz] using hC z
    else
      have hC0 : (0 : ℝ) ≤ C := (norm_nonneg (g z)).trans (hC z)
      simpa [ι, hz] using hC0
  have hmap := Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₀ θ t
  have : IsProbabilityMeasure ((M θ).map (s t)) := inferInstance
  have hInt : Integrable (fun z : ℝ × 𝒮 × 𝒜 => ι z * g z) (M.stageK θ ∘ₘ (M θ).map (s t)) :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hCf)
  have e1 : ∫ ω, (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) * g (ω t) ∂(M θ) =
      ∫ z, ι z * g z ∂((M θ).map (fun ω => ω t)) := by
    exact (integral_map (μ := M θ) (φ := fun ω : ℕ → ℝ × 𝒮 × 𝒜 => ω t)
      (f := fun z : ℝ × 𝒮 × 𝒜 => ι z * g z)
      (measurable_pi_apply t).aemeasurable hf.aestronglyMeasurable).symm
  rw [e1, hmap, Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
  have hinner : ∀ y, ∫ z, ι z * g z ∂(M.stageK θ y) =
      if y = sₜ then
        M.π θ sₜ aₜ * ReferenceMeasure.measure.real {aₜ} *
          ∫ ρ, g (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ))
      else 0 := by
    intro y
    have e :=
      Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hCf θ y
    rw [e]
    have hρ : ∀ u', ∫ ρ, ι (ρ, y, u') * g (ρ, y, u') ∂(M.reward (y, u')) =
        if y = sₜ ∧ u' = aₜ then ∫ ρ, g (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)) else 0 := by
      intro u'
      if hyu : y = sₜ ∧ u' = aₜ then
        obtain ⟨hy, hu⟩ := hyu
        subst hy
        subst hu
        simp only [ι, and_self, ite_true, one_mul]
      else
        have h0 : ∀ ρ, ι (ρ, y, u') * g (ρ, y, u') = 0 := by
          intro ρ
          simp [ι, hyu]
        rw [show (fun ρ => ι (ρ, y, u') * g (ρ, y, u') ) = fun _ => 0 from funext h0,
          MeasureTheory.integral_zero]
        simp [hyu]
    simp_rw [hρ, smul_eq_mul]
    if hy : y = sₜ then
      have hfun : (fun u' : 𝒜 =>
          M.π θ y u' * (if y = sₜ ∧ u' = aₜ then
            ∫ ρ, g (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)) else 0)) =
          ({aₜ} : Set 𝒜).indicator (fun _ =>
            M.π θ sₜ aₜ * ∫ ρ, g (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ))) := by
        funext u'
        by_cases hu : u' = aₜ <;> simp [hu, hy, Set.indicator]
      rw [hfun, integral_indicator (measurableSet_singleton aₜ), MeasureTheory.setIntegral_const,
        smul_eq_mul, hy]
      simp
      ring
    else
      simp [hy]
  simp_rw [hinner]
  have hI : (fun y : 𝒮 =>
      if y = sₜ then
        M.π θ sₜ aₜ * ReferenceMeasure.measure.real {aₜ} *
          ∫ ρ, g (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ))
      else 0) =
      ({sₜ} : Set 𝒮).indicator (fun _ =>
        M.π θ sₜ aₜ * ReferenceMeasure.measure.real {aₜ} *
          ∫ ρ, g (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ))) := by
    funext y
    by_cases hy : y = sₜ <;> simp [hy, Set.indicator]
  rw [hI, integral_indicator (measurableSet_singleton sₜ), MeasureTheory.setIntegral_const, smul_eq_mul]
  ring

/--
On a reachable state-action pair at time `t`
(`ℙ(s[t] = x ∧ a[t] = u) ≠ 0`):
`Q θ γ t x u = rkd x u + γ * ∫ y, V0 θ γ y ∂(trans (x, u))`.
This is the time-`t` form of
[Q0 = rkd + γ ∫ V0](?module=Random.Qkd.eq.AddRkd_MulIntegral_Vkd.of.Ne0Real_Joint.In_Ico),
which is the special case `t = 0`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {θ : Θ}
  {t : ℕ}
  {sₜ : 𝒮}
  {aₜ : 𝒜}
  {R : ℝ}
-- given
  (h : γ ∈ Set.Ico 0 1)
  (hQA : (M θ).real
    (((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω t).2.1) ⁻¹' {sₜ}) ∩
      ((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω t).2.2) ⁻¹' {aₜ})) ≠ 0)
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1) :
-- imply
  M.Q θ γ t sₜ aₜ = M.rkd R sₜ aₜ + γ * ∫ y, M.V0 R θ γ y ∂(M.trans (sₜ, aₜ)) := by
-- proof
  classical
  let r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω => (ω t).2.1
  let a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω => (ω t).2.2
  have h₀ : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => rfl
  let B : Set (ℕ → ℝ × 𝒮 × 𝒜) :=
    ((fun ω => (ω t).2.1) ⁻¹' {sₜ}) ∩ ((fun ω => (ω t).2.2) ⁻¹' {aₜ})
  have hBm : MeasurableSet B :=
    ((measurable_pi_apply t).snd.fst (measurableSet_singleton sₜ)).inter
      ((measurable_pi_apply t).snd.snd (measurableSet_singleton aₜ))
  unfold Model.Q
  simp only [Expectation.asRV_process]
  have hpR : Measurable (fun ω k ↦ r k ω) :=
    Measurable.of_eval fun k => measurable_fst.comp (measurable_pi_apply k)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) := by
    unfold Dot.dot Function.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  have hy : Measurable (s t, a t) :=
    ((measurable_pi_apply t).snd.fst).prodMk ((measurable_pi_apply t).snd.snd)
  have hpre₀ : (s t, a t) ⁻¹' {(sₜ, aₜ)} =
      (fun ω => (ω t).2.1) ⁻¹' {sₜ} ∩ (fun ω => (ω t).2.2) ⁻¹' {aₜ} := by
    ext ω
    simp [JointRandomSymbol, s, a, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_singleton_iff, Prod.ext_iff]
  have hmap : (M θ).map (s t, a t) {(sₜ, aₜ)} ≠ 0 := by
    rw [Measure.map_apply hy (measurableSet_singleton (sₜ, aₜ)), hpre₀]
    exact fun hz => hQA (by simp [Measure.real, hz])
  rw [Expectation.condEval_eq_integral hpR hy hfG hmap]
  have hpre : (s t, a t) ⁻¹' {(sₜ, aₜ)} = B := by
    ext ω
    simp [JointRandomSymbol, B, s, a, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_singleton_iff, Prod.ext_iff]
  rw [hpre]
  have hdot : ∀ ω, (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun k => r k ω)[t:] = ∑' k, γ ^ k * r (t + k) ω := by
    intro ω
    change ∑' k, (γ ^ (id : ℕ → ℕ)) k * (fun k => r k ω)[t:] k = _
    unfold Function.getSliceFrom Function.instHPowNatSeq
    simp only [id_eq]
  simp_rw [hdot]
  have hcond : ∀ {f : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ},
      ∫ ω, f ω ∂(M θ)[|B] =
        ((M θ).real B)⁻¹ * ∫ ω, B.indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) ω * f ω ∂(M θ) := by
    intro f
    rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hBm, ENNReal.toReal_inv,
      ← measureReal_def, smul_eq_mul]
    congr 1
    congr 1
    funext ω
    by_cases hω : ω ∈ B <;> simp [hω]
  have hswap : ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|B] =
      ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|B] := by
    if hB0 : (M θ) B = 0 then
      simp [cond_eq_zero_of_meas_eq_zero hB0]
    else
      have := cond_isProbabilityMeasure (μ := M θ) hB0
      have hae : ∀ᵐ ω ∂(M θ)[|B], ∀ k, ‖r (t + k) ω‖ ≤ |R| := by
        apply cond_absolutelyContinuous.ae_le
        exact ae_all_iff.2 fun k =>
          (MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₀ hR θ (t + k)).mono fun ω hω => by
            rw [hω]
            exact NormClip.le.Abs_R R (ω (t + k)).1
      have hm : ∀ k, Measurable (r (t + k)) :=
        fun k => measurable_fst.comp (measurable_pi_apply (t + k))
      have hF : ∀ k, Integrable (fun ω => γ ^ k * r (t + k) ω) (M θ)[|B] := fun k =>
        Integrable.of_bound ((hm k).const_mul (γ ^ k)).aestronglyMeasurable (γ ^ k * |R|)
          (hae.mono fun ω hω => by
            rw [norm_mul, norm_pow, Real.norm_of_nonneg h.1]
            exact mul_le_mul_of_nonneg_left (hω k) (pow_nonneg h.1 k))
      have hS : Summable (fun k => ∫ ω, ‖γ ^ k * r (t + k) ω‖ ∂(M θ)[|B]) := by
        refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) (fun k => ?_)
          ((summable_geometric_of_lt_one h.1 h.2).mul_right |R|)
        have hb : ∀ᵐ ω ∂(M θ)[|B], ‖‖γ ^ k * r (t + k) ω‖‖ ≤ γ ^ k * |R| :=
          hae.mono fun ω hω => by
            rw [norm_norm, norm_mul, norm_pow, Real.norm_of_nonneg h.1]
            exact mul_le_mul_of_nonneg_left (hω k) (pow_nonneg h.1 k)
        have := norm_integral_le_of_norm_le_const hb
        simp only [probReal_univ, mul_one] at this
        exact (Real.le_norm_self _).trans this
      rw [← (hasSum_integral_of_summable_integral_norm hF hS).tsum_eq]
      congr 1
      funext k
      exact integral_const_mul _ _
  rw [hswap]
  let clipf : ℝ × 𝒮 × 𝒜 → ℝ := fun w ↦ clip w.1 (-R) R
  have hf : StronglyMeasurable clipf := by
    unfold clipf clip
    exact ((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable
  have hC : ∀ w, ‖clipf w‖ ≤ |R| := fun w => NormClip.le.Abs_R R w.1
  have hι : ∀ ω, B.indicator (1 : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ) ω =
      if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0 := by
    intro ω
    by_cases hω : (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ <;> simp [B, hω, Set.indicator]
  have hq : ∀ k, ∫ ω, r (t + k) ω ∂(M θ)[|B] =
      ∫ ρ, M.Kf θ clipf k (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)) := by
    intro k
    rw [hcond]
    simp_rw [hι]
    have hclip : (fun ω => (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) * r (t + k) ω) =ᵐ[M θ]
        fun ω => (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) * clipf (ω (t + k)) := by
      filter_upwards [MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₀ hR θ (t + k)] with ω hω
      rw [hω]
    rw [integral_congr_ae hclip]
    let G : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → ℝ :=
      fun hist => if (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = sₜ ∧
        (hist ⟨t, mem_Iic.2 le_rfl⟩).2.2 = aₜ then 1 else 0
    have hG : StronglyMeasurable G := by
      have hset : MeasurableSet {hist : Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜 |
          (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = sₜ ∧ (hist ⟨t, mem_Iic.2 le_rfl⟩).2.2 = aₜ} :=
        ((measurable_pi_apply _).snd.fst (measurableSet_singleton sₜ)).inter
          ((measurable_pi_apply _).snd.snd (measurableSet_singleton aₜ))
      have hιG : StronglyMeasurable (fun hist : Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜 =>
          if hist ∈ {hist | (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = sₜ ∧
            (hist ⟨t, mem_Iic.2 le_rfl⟩).2.2 = aₜ} then (1 : ℝ) else 0) :=
        (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
      have hιG' : G = fun hist =>
          if hist ∈ {hist : Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜 |
            (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = sₜ ∧
              (hist ⟨t, mem_Iic.2 le_rfl⟩).2.2 = aₜ} then (1 : ℝ) else 0 := by
        funext hist
        simp [G]
      exact hιG'.symm ▸ hιG
    have hCG : ∀ hist, ‖G hist‖ ≤ 1 := by
      intro hist
      if hh : (hist ⟨t, mem_Iic.2 le_rfl⟩).2.1 = sₜ ∧
          (hist ⟨t, mem_Iic.2 le_rfl⟩).2.2 = aₜ then
        simp [G, hh]
      else
        simp [G, hh]
    have hmark :=
      All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ k t hG hCG
    have hGapp : ∀ ω : ℕ → ℝ × 𝒮 × 𝒜,
        G (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω) =
          if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0 := by
      intro ω
      unfold G
      refine ite_congr ?_ (fun _ => rfl) (fun _ => rfl)
      simp [Preorder.frestrictLe_apply]
    have hKf :=
      StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ k
    have hpull : ∫ ω, (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) * clipf (ω (t + k)) ∂(M θ) =
        (M θ).real B *
          ∫ ρ, M.Kf θ clipf k (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)) := by
      have hωk : (fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
          (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) * clipf (ω (t + k))) =
          fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
            G (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω) * clipf (ω (t + k)) := by
        funext ω
        simp [hGapp]
      rw [hωk]
      rw [hmark]
      have happ : (fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
          G (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω) * M.Kf θ clipf k (ω t)) =
          fun ω => (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) *
            M.Kf θ clipf k (ω t) := by
        funext ω; simp [hGapp]
      rw [happ]
      have hslice := joint_disint (M := M) h₀ hKf.1 hKf.2 θ t sₜ aₜ
      have hreal : (M θ).real B =
          ((M θ).map (s t)).real {sₜ} * M.π θ sₜ aₜ *
            ReferenceMeasure.measure.real {aₜ} := by
        have hone := joint_disint (M := M) h₀
          (g := fun _ : ℝ × 𝒮 × 𝒜 => (1 : ℝ)) (C := 1)
          stronglyMeasurable_const (fun _ => by simp) θ t sₜ aₜ
        have hind : ∫ ω, (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) ∂(M θ) =
            (M θ).real B := by
          have heq : (fun ω => if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) =
              B.indicator (fun _ => (1 : ℝ)) := by
            funext ω
            if hω : (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then
              have hmem : ω ∈ B := by
                simpa [B, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] using hω
              simp [hmem, hω, Set.indicator]
            else
              have hmem : ω ∉ B := by
                simpa [B, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] using hω
              simp [hmem, hω, Set.indicator]
          rw [heq, integral_indicator hBm, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
        have hrew : ∫ ω, (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) * (1 : ℝ) ∂(M θ) =
            ∫ ω, (if (ω t).2.1 = sₜ ∧ (ω t).2.2 = aₜ then (1 : ℝ) else 0) ∂(M θ) := by
          simp
        rw [hrew] at hone
        have : IsProbabilityMeasure ((M.reward (sₜ, aₜ) : Measure ℝ)) := inferInstance
        rw [hind] at hone
        simpa [MeasureTheory.integral_const, probReal_univ, one_smul] using hone
      rw [hslice, hreal]
    rw [hpull, inv_mul_cancel_left₀ hQA]
  simp_rw [hq]
  have hq0 : ∫ ρ, M.Kf θ clipf 0 (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)) = M.rkd R sₜ aₜ := by
    simp [clipf, Model.Kf, Model.rkd]
  have hqS : ∀ k, ∫ ρ, M.Kf θ clipf (k + 1) (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)) =
      ∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, aₜ)) := by
    intro k
    have hz : ∀ ρ, M.Kf θ clipf (k + 1) (ρ, sₜ, aₜ) =
        ∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, aₜ)) :=
      fun ρ => Kf_succ_eq_Wkd (M := M) R θ k (ρ, sₜ, aₜ)
    simp_rw [hz]
    have : IsProbabilityMeasure ((M.reward (sₜ, aₜ) : Measure ℝ)) := inferInstance
    rw [MeasureTheory.integral_const, probReal_univ, one_smul]
  have hsum : Summable (fun k => γ ^ k * ∫ ρ, M.Kf θ clipf k (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ))) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h.1 h.2).mul_right |R|) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h.1]
    have hμ : IsProbabilityMeasure ((M.reward (sₜ, aₜ) : Measure ℝ)) := inferInstance
    have hpt : ∀ ρ, ‖M.Kf θ clipf k (ρ, sₜ, aₜ)‖ ≤ |R| := by
      intro ρ
      have hKf :=
        StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hf hC θ k
      simpa [norm_norm] using hKf.2 (ρ, sₜ, aₜ)
    have hle := norm_integral_le_of_norm_le_const (μ := M.reward (sₜ, aₜ)) (C := |R|)
      (Filter.Eventually.of_forall hpt)
    simp only [probReal_univ, mul_one] at hle
    exact mul_le_mul_of_nonneg_left hle (pow_nonneg h.1 k)
  rw [(hsum.tsum_eq_zero_add)]
  rw [hq0, pow_zero, one_mul]
  have htail : ∑' k, γ ^ (k + 1) *
      ∫ ρ, M.Kf θ clipf (k + 1) (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)) =
      γ * ∫ y, M.V0 R θ γ y ∂(M.trans (sₜ, aₜ)) := by
    simp_rw [hqS]
    have hre : ∀ k, γ ^ (k + 1) * ∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, aₜ)) =
        γ * (γ ^ k * ∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, aₜ))) := by
      intro k
      rw [pow_succ]
      ring
    simp_rw [hre]
    rw [tsum_mul_left]
    have hmeas : ∀ k, Measurable (M.Wkd R θ k) := fun k =>
      Measurable_Wkd.of.All_Measurable_Prob (M := M) (fun θ' => hStoch.measurable_π θ') R θ k
    have hbd : ∀ k y, ‖γ ^ k * M.Wkd R θ k y‖ ≤ γ ^ k * |R| := fun k y => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h.1]
      exact mul_le_mul_of_nonneg_left (NormWkd.le.Abs_R (M := M) R θ k y) (pow_nonneg h.1 k)
    have hri : ∀ k, Integrable (fun y => γ ^ k * M.Wkd R θ k y) (M.trans (sₜ, aₜ)) := fun k =>
      Integrable.of_bound ((hmeas k).const_mul _).aestronglyMeasurable (γ ^ k * |R|)
        (Filter.Eventually.of_forall fun y => hbd k y)
    have hSn : Summable (fun k => ∫ y, ‖γ ^ k * M.Wkd R θ k y‖ ∂(M.trans (sₜ, aₜ))) := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
        ((summable_geometric_of_lt_one h.1 h.2).mul_right |R|)
      have hμ : IsProbabilityMeasure ((M.trans (sₜ, aₜ) : Measure 𝒮)) := inferInstance
      calc
        _ ≤ ∫ _, γ ^ k * |R| ∂(M.trans (sₜ, aₜ)) :=
          integral_mono_ae (hri k).norm (integrable_const _)
            (Filter.Eventually.of_forall fun y => hbd k y)
        _ = γ ^ k * |R| := by
          simp [MeasureTheory.integral_const, probReal_univ]
    simp_rw [← integral_const_mul, Model.V0]
    rw [integral_tsum_of_summable_integral_norm hri hSn]
    rw [← integral_const_mul]
  rw [htail]


-- created on 2026-11-13
-- updated on 2026-11-18
