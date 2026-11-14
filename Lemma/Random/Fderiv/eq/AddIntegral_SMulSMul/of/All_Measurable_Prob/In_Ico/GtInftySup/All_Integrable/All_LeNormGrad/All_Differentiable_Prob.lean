import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Random.Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob
import Lemma.Random.DifferentiableAt.Fderiv.eq.SMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Measurable_Qkd.of.All_Measurable_Prob
import Lemma.Random.Qkd.eq.AddRkd_MulIntegral_Vkd.of.Ne0Real_Joint.In_Ico
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.MeasurableRkd
import Lemma.Random.NormQkd.le.AddAbs_RMulInvSub1Abs_R.of.In_Ico
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory PolicyGradient Random Real
set_option maxHeartbeats 900000


/--
gradient of the Bellman equation for the closed-form value function with continuous states and a density policy:
`fderiv V0(x) = ∫ u, Q0(x, u) • fderiv π(u | x) du + γ • ∫ u, π(u | x) • ∫ y, fderiv V0(y) ∂T(· | x, u) du`.
Both action sums become integrals against the reference measure of `𝒜` (differentiated under the integral sign).
`h₀`, `h₁`: `θ ↦ π_θ(u | x)` is differentiable and its gradient is dominated by `g x u`; `h₂`, `h₃`: `g x` is integrable
over the actions, uniformly in the state (this replaces `|𝒜| * sup ‖∇π‖ < ∞` of the finite-action version);
`h₅`: `(x, u) ↦ π_θ(u | x)` is jointly measurable.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₁ : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u)
  (h₂ : ∀ x, Integrable (g x) μ.measure)
  (h₃ : sup[x] ∫ u, g x u ∂μ.measure < ∞)
  (h₄ : γ ∈ Set.Ico 0 1)
  (h₅ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (hQA : ∀ θ x u,
    (M θ).real
      (((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω 0).2.1) ⁻¹' {x}) ∩
        ((fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (ω 0).2.2) ⁻¹' {u})) ≠ 0)
  (x : 𝒮)
  (θ : Θ) :
-- imply
  fderiv ℝ (fun θ => M.V0 θ γ x) θ =
    ∫ u, M.Q0 θ γ x u • fderiv ℝ (fun θ => M.policy.prob θ x u) θ ∂μ.measure +
      γ • ∫ u, M.policy.prob θ x u • ∫ y, fderiv ℝ (fun θ => M.V0 θ γ y) θ ∂(M.env.trans (x, u)) ∂μ.measure := by
-- proof
  have := M.env.trans_markov
  obtain ⟨Cg, hCg⟩ := id h₃
  have hg : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg := fun x => hCg ⟨x, rfl⟩
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using h₁ θ x u
  obtain ⟨C, hCV⟩ := GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ h₄ h₅
  have hQ := fun u θ => DifferentiableAt.Fderiv.eq.SMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ h₄ h₅ hQA x u θ
  have hQb : ∀ θ u, ‖M.Q0 θ γ x u‖ ≤ |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) :=
    fun θ u =>
      NormQkd.le.AddAbs_RMulInvSub1Abs_R.of.In_Ico (M := M) h₄ θ x u <| by
        intro h0
        exact hQA θ x u (by simp [Measure.real, h0])
  have hQ' : ∀ θ u, ‖fderiv ℝ (fun θ => M.Q0 θ γ x u) θ‖ ≤ γ * C := fun θ u => by
    have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u)) (C := C)
      (f := fun y => fderiv ℝ (fun θ => M.V0 θ γ y) θ) (Filter.Eventually.of_forall fun y => by
        have h := hCV ⟨(θ, y), rfl⟩
        simpa [gradient, LinearIsometryEquiv.norm_map] using h)
    rw [(hQ u θ).2, norm_smul, Real.norm_of_nonneg h₄.1]
    exact mul_le_mul_of_nonneg_left (by simpa using h) h₄.1
  have hD := HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
    (ν := ReferenceMeasure.measure) (f := fun θ u => M.policy.prob θ x u)
    (G := fun θ u => M.Q0 θ γ (x, u).1 (x, u).2) (g := g x)
    (B₀ := |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|)) (B₁ := γ * C)
    (fun θ => (h₅ θ).comp (measurable_prodMk_left (x := x))) (h₀ x) (fun θ u => M.policy.nonneg θ x u)
    (fun θ => M.policy.integral_eq_one θ x) (fun θ u => hC θ x u) (h₂ x)
    (fun θ => (Measurable_Qkd.of.All_Measurable_Prob (M := M) h₅ h₄
      (fun y u => hQA θ y u)).comp (measurable_prodMk_left (x := x)))
    (fun u θ => (hQ u θ).1) hQb hQ' θ
  have hb : (fun θ => M.V0 θ γ x) = fun θ => ∫ u, M.policy.prob θ x u * M.Q0 θ γ x u ∂ReferenceMeasure.measure := by
    funext θ'
    have hB := Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob (M := M) h₅ h₄ θ' x
    have hπi : Integrable (M.policy.prob θ' x) ReferenceMeasure.measure :=
      Integrable.of_integral_ne_zero (by rw [M.policy.integral_eq_one θ' x]; exact one_ne_zero)
    have hπm : Measurable (M.policy.prob θ' x) := (h₅ θ').comp measurable_prodMk_left
    have hr : Integrable (fun u => M.policy.prob θ' x u * M.rkd x u) ReferenceMeasure.measure :=
      (hπi.mul_const |M.env.R|).mono'
        (hπm.mul ((MeasurableRkd (M := M)).comp measurable_prodMk_left)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by
          rw [norm_mul, Real.norm_of_nonneg (M.policy.nonneg θ' x u)]
          exact mul_le_mul_of_nonneg_left (NormRkd.le.Abs_R (M := M) x u) (M.policy.nonneg θ' x u))
    have hTm : Measurable (fun u => ∫ y, M.V0 θ' γ y ∂(M.env.trans (x, u))) :=
      ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
        (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.V0 θ' γ z.2)
        ((Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ' γ).stronglyMeasurable.comp_measurable
          measurable_snd)).measurable).comp measurable_prodMk_left
    have hv : Integrable (fun u => M.policy.prob θ' x u * ∫ y, M.V0 θ' γ y ∂(M.env.trans (x, u)))
        ReferenceMeasure.measure :=
      (hπi.mul_const ((1 - γ)⁻¹ * |M.env.R|)).mono' (hπm.mul hTm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by
          have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
            (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₄ θ' y)
          rw [norm_mul, Real.norm_of_nonneg (M.policy.nonneg θ' x u)]
          exact mul_le_mul_of_nonneg_left (by simpa using h) (M.policy.nonneg θ' x u))
    have e : (fun u => M.policy.prob θ' x u * M.Q0 θ' γ x u) =
        fun u => M.policy.prob θ' x u * M.rkd x u +
          γ * (M.policy.prob θ' x u * ∫ y, M.V0 θ' γ y ∂(M.env.trans (x, u))) := by
      funext u
      rw [Qkd.eq.AddRkd_MulIntegral_Vkd.of.Ne0Real_Joint.In_Ico
        (M := M) h₄ (hQA θ' x u)]
      ring
    rw [hB, e, integral_add hr (hv.const_mul γ), integral_const_mul]
  have hV : HasFDerivAt (fun θ => M.V0 θ γ x)
      (∫ u, M.policy.prob θ x u • fderiv ℝ (fun θ => M.Q0 θ γ x u) θ ∂ReferenceMeasure.measure +
        ∫ u, M.Q0 θ γ x u • fderiv ℝ (fun θ => M.policy.prob θ x u) θ ∂ReferenceMeasure.measure) θ := by
    rw [hb]
    exact hD.1
  have hπQ : ∫ u, M.policy.prob θ x u • fderiv ℝ (fun θ => M.Q0 θ γ x u) θ ∂ReferenceMeasure.measure =
      γ • ∫ u, M.policy.prob θ x u • ∫ y, fderiv ℝ (fun θ => M.V0 θ γ y) θ ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure := by
    rw [← integral_smul]
    congr 1
    funext u
    rw [(hQ u θ).2, smul_comm]
  rw [hV.fderiv, hπQ, add_comm]


/--
Same gradient identity with the closed form `rkd + γ * ∫ V0` in place of `Q0`, so the joint atom is not required.
-/
lemma bellmanFderivClosed
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₁ : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u)
  (h₂ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₃ : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞)
  (h₄ : γ ∈ Set.Ico 0 1)
  (h₅ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (x : 𝒮)
  (θ : Θ) :
  fderiv ℝ (fun θ => M.V0 θ γ x) θ =
    ∫ u, (M.rkd x u + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (x, u))) •
        fderiv ℝ (fun θ => M.policy.prob θ x u) θ ∂ReferenceMeasure.measure +
      γ • ∫ u, M.policy.prob θ x u •
        ∫ y, fderiv ℝ (fun θ => M.V0 θ γ y) θ ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure := by
  have := M.env.trans_markov
  obtain ⟨Cg, hCg⟩ := id h₃
  have hg : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg := fun x => hCg ⟨x, rfl⟩
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using h₁ θ x u
  obtain ⟨C, hCV⟩ :=
    GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₀ h₁ h₂ h₃ h₄ h₅
  let Qf (θ' : Θ) (u : 𝒜) : ℝ :=
    M.rkd x u + γ * ∫ y, M.V0 θ' γ y ∂(M.env.trans (x, u))
  have hVfd :=
    HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₀ h₁ h₂ h₃ h₄ h₅
  have hI : ∀ θ' u, HasFDerivAt (fun θ'' => ∫ y, M.V0 θ'' γ y ∂(M.env.trans (x, u)))
      (∫ y, fderiv ℝ (fun θ'' => M.V0 θ'' γ y) θ' ∂(M.env.trans (x, u))) θ' := fun θ' u =>
    hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun θ'' y => M.V0 θ'' γ y)
      (F' := fun θ'' y => fderiv ℝ (fun θ'' => M.V0 θ'' γ y) θ'') (s := Set.univ) (bound := fun _ => C)
      Filter.univ_mem
      (Filter.Eventually.of_forall fun θ'' =>
        (Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ'' γ).aestronglyMeasurable)
      (Integrable.of_bound (Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ' γ).aestronglyMeasurable
        ((1 - γ)⁻¹ * |M.env.R|)
        (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₄ θ' y))
      (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
        (fun θ'' => Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ'' γ)
        (fun y => (hVfd y θ').differentiableAt)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y θ'' _ => by
        have h := hCV ⟨(θ'', y), rfl⟩
        simpa [gradient, LinearIsometryEquiv.norm_map] using h)
      (integrable_const _)
      (Filter.Eventually.of_forall fun y θ'' _ => (hVfd y θ'').differentiableAt.hasFDerivAt)
  have hQ : ∀ u θ', DifferentiableAt ℝ (fun θ'' => Qf θ'' u) θ' ∧
      fderiv ℝ (fun θ'' => Qf θ'' u) θ' =
        γ • ∫ y, fderiv ℝ (fun θ'' => M.V0 θ'' γ y) θ' ∂(M.env.trans (x, u)) := fun u θ' => by
    have hEq : (fun θ'' => Qf θ'' u) =
        fun θ'' => M.rkd x u + γ * ∫ y, M.V0 θ'' γ y ∂(M.env.trans (x, u)) := rfl
    rw [hEq]
    refine ⟨((hI θ' u).differentiableAt.const_mul γ).const_add _, ?_⟩
    rw [fderiv_const_add, fderiv_const_mul (hI θ' u).differentiableAt, (hI θ' u).fderiv]
  have hQb : ∀ θ' u, ‖Qf θ' u‖ ≤ |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) := fun θ' u => by
    refine (norm_add_le _ _).trans ?_
    refine add_le_add (NormRkd.le.Abs_R (M := M) x u) ?_
    rw [norm_mul, Real.norm_of_nonneg h₄.1]
    exact mul_le_mul_of_nonneg_left
      ((norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun y =>
          NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₄ θ' y)).trans_eq (by simp))
      h₄.1
  have hQ' : ∀ θ' u, ‖fderiv ℝ (fun θ'' => Qf θ'' u) θ'‖ ≤ γ * C := fun θ' u => by
    have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u)) (C := C)
      (f := fun y => fderiv ℝ (fun θ'' => M.V0 θ'' γ y) θ')
      (Filter.Eventually.of_forall fun y => by
        have h := hCV ⟨(θ', y), rfl⟩
        simpa [gradient, LinearIsometryEquiv.norm_map] using h)
    rw [(hQ u θ').2, norm_smul, Real.norm_of_nonneg h₄.1]
    exact mul_le_mul_of_nonneg_left (by simpa using h) h₄.1
  have hQm : ∀ θ', Measurable (fun u => Qf θ' u) := fun θ' => by
    apply Measurable.add
    · exact (MeasurableRkd (M := M)).comp measurable_prodMk_left
    · apply Measurable.const_mul
      exact ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
        (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.V0 θ' γ z.2)
        ((Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ' γ).stronglyMeasurable.comp_measurable
          measurable_snd)).measurable).comp measurable_prodMk_left
  have hD := HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
    (ν := ReferenceMeasure.measure) (f := fun θ' u => M.policy.prob θ' x u)
    (G := fun θ' u => Qf θ' u) (g := g x)
    (B₀ := |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|)) (B₁ := γ * C)
    (fun θ' => (h₅ θ').comp (measurable_prodMk_left (x := x))) (h₀ x) (fun θ' u => M.policy.nonneg θ' x u)
    (fun θ' => M.policy.integral_eq_one θ' x) (fun θ' u => hC θ' x u) (h₂ x)
    hQm
    (fun u θ' => (hQ u θ').1) hQb hQ' θ
  have hb : (fun θ' => M.V0 θ' γ x) =
      fun θ' => ∫ u, M.policy.prob θ' x u * Qf θ' u ∂ReferenceMeasure.measure := by
    funext θ'
    have hB := Vkd.eq.Integral_MulProbQkd.of.In_Ico.All_Measurable_Prob (M := M) h₅ h₄ θ' x
    have hπi : Integrable (M.policy.prob θ' x) ReferenceMeasure.measure :=
      Integrable.of_integral_ne_zero (by rw [M.policy.integral_eq_one θ' x]; exact one_ne_zero)
    have hπm : Measurable (M.policy.prob θ' x) := (h₅ θ').comp measurable_prodMk_left
    have hr : Integrable (fun u => M.policy.prob θ' x u * M.rkd x u) ReferenceMeasure.measure :=
      (hπi.mul_const |M.env.R|).mono'
        (hπm.mul ((MeasurableRkd (M := M)).comp measurable_prodMk_left)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by
          rw [norm_mul, Real.norm_of_nonneg (M.policy.nonneg θ' x u)]
          exact mul_le_mul_of_nonneg_left (NormRkd.le.Abs_R (M := M) x u) (M.policy.nonneg θ' x u))
    have hTm : Measurable (fun u => ∫ y, M.V0 θ' γ y ∂(M.env.trans (x, u))) :=
      ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.env.trans)
        (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.V0 θ' γ z.2)
        ((Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ' γ).stronglyMeasurable.comp_measurable
          measurable_snd)).measurable).comp measurable_prodMk_left
    have hv : Integrable (fun u => M.policy.prob θ' x u * ∫ y, M.V0 θ' γ y ∂(M.env.trans (x, u)))
        ReferenceMeasure.measure :=
      (hπi.mul_const ((1 - γ)⁻¹ * |M.env.R|)).mono' (hπm.mul hTm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by
          have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
            (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₄ θ' y)
          rw [norm_mul, Real.norm_of_nonneg (M.policy.nonneg θ' x u)]
          exact mul_le_mul_of_nonneg_left (by simpa using h) (M.policy.nonneg θ' x u))
    have e : (fun u => M.policy.prob θ' x u * Qf θ' u) =
        fun u => M.policy.prob θ' x u * M.rkd x u +
          γ * (M.policy.prob θ' x u * ∫ y, M.V0 θ' γ y ∂(M.env.trans (x, u))) := by
      funext u
      ring
    rw [hB, e, integral_add hr (hv.const_mul γ), integral_const_mul]
  have hVf : HasFDerivAt (fun θ' => M.V0 θ' γ x)
      (∫ u, M.policy.prob θ x u • fderiv ℝ (fun θ' => Qf θ' u) θ ∂ReferenceMeasure.measure +
        ∫ u, Qf θ u • fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ ∂ReferenceMeasure.measure) θ := by
    rw [hb]
    exact hD.1
  have hπQ : ∫ u, M.policy.prob θ x u • fderiv ℝ (fun θ' => Qf θ' u) θ ∂ReferenceMeasure.measure =
      γ • ∫ u, M.policy.prob θ x u •
        ∫ y, fderiv ℝ (fun θ' => M.V0 θ' γ y) θ ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure := by
    rw [← integral_smul]
    congr 1
    funext u
    rw [(hQ u θ).2, smul_comm]
  rw [hVf.fderiv, hπQ, add_comm]


-- created on 2026-10-07
-- updated on 2026-11-14
