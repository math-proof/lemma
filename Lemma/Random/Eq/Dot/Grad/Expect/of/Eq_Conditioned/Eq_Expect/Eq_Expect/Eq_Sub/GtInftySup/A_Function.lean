import Notation.Fun
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.All_Eq_Joint.All_EqWithDensity.In_Ico
import Lemma.Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Syntax.Order.Sup
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 800000


/-- Discounted score expectation equals the observation integral. -/
lemma expect_weight_score_eq_integral
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {W : ℕ → 𝒮 → 𝒜 → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (hsP : PSpace (M θ) (AsPathRV.path s))
  (haP : PSpace (M θ) (AsPathRV.path a)) :
-- imply
  𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      W t s[t] a[t] • ∇[θ] Real.log (M.policy.prob θ s[t] a[t])) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      W t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) := by
-- proof
  have : PSpace (M θ) (AsPathRV.path s) := hsP
  have : PSpace (M θ) (AsPathRV.path a) := haP
  rw [Expectation.ofRV, expectation_bochner]
  have hx : AEMeasurable (AsPathRV.path s, AsPathRV.path a) (M θ) :=
    PSpace.aemeasurable
  refine (integral_map hx ?_).trans ?_
  ·
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    refine (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t => ?_).aestronglyMeasurable
    exact StronglyMeasurable.comp_measurable
      (f := fun q : 𝒮 × 𝒜 ↦
        γ ^ t • W t q.1 q.2 • ∇[θ] Real.log (M.policy.prob θ q.1 q.2))
      StronglyMeasurable.of_discrete
      (show Measurable fun p : (ℕ → 𝒮) × (ℕ → 𝒜) ↦ (p.1 t, p.2 t) from
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          ((measurable_pi_apply t).comp measurable_snd))
  ·
    simp only [JointRandomSymbol, AsPathRV.path_fun, Dot.dot, Function.hPow_apply, id_eq]


/-- A state-dependent baseline has policy-score integral zero, so it drops out of the gradient. -/
private lemma integral_state_score_zero
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {g : 𝒮 → 𝒜 → ℝ}
  {C Ms : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₂ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₃ : ∀ x, Integrable (g x) μ.measure)
  (h : 𝒮 → ℝ)
  (hh : Measurable h)
  (hC : ∀ y, ‖h y‖ ≤ C)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms)
  (t : ℕ) :
-- imply
  ∫ ω, h (s[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))
    ∂(M θ) = 0 := by
-- proof
  let e := (InnerProductSpace.toDual ℝ Θ).symm
  have hfd :
    ∫ ω, h (s[t] ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s[t] ω) (a[t] ω))) θ
      ∂(M θ) = 0 :=
    Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
      (M := M) (r := r.toFun) (s := s.toFun) (a := a.toFun) θ h₀ h₁ h₂ h₃ h hh hC hφ hMs t
  have hfun :
    (fun ω => h (s[t] ω) • ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) =
      fun ω => e (h (s[t] ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s[t] ω) (a[t] ω))) θ) := by
    funext ω
    simp [e, gradient, map_smul]
  have hint :
    Integrable (fun ω => h (s[t] ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s[t] ω) (a[t] ω))) θ)
      (M θ) := by
    have hmeas : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s[t] ω, a[t] ω)) :=
      (Measurable.of.All_Eq.snd.fst h₀ t).prodMk (Measurable.of.All_Eq.snd.snd h₀ t)
    have hbound : ∀ ω,
      ‖h (s[t] ω) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s[t] ω) (a[t] ω))) θ‖ ≤
        max C 0 * max Ms 0 := by
      intro ω
      rw [norm_smul]
      apply mul_le_mul
      · apply (hC (s[t] ω)).trans (le_max_left _ _)
      · apply (hMs (s[t] ω) (a[t] ω)).trans (le_max_left _ _)
      · apply norm_nonneg
      · apply le_max_right
    refine Integrable.of_bound ?_ (max C 0 * max Ms 0) (Filter.Eventually.of_forall hbound)
    exact (StronglyMeasurable.comp_measurable
      (f := fun q : 𝒮 × 𝒜 =>
        h q.1 • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' q.1 q.2)) θ)
      StronglyMeasurable.of_discrete hmeas).aestronglyMeasurable
  rw [hfun]
  let eCLM := e.toContinuousLinearEquiv.toContinuousLinearMap
  change ∫ ω, eCLM
    (h (s[t] ω) • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s[t] ω) (a[t] ω))) θ)
    ∂(M θ) = 0
  rw [eCLM.integral_comp_comm hint, hfd, map_zero]


/-- One time step of a score, weighted by a real function of the visited state and action, is integrable. -/
lemma integrable_weight_score
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {B Ms : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {W : 𝒮 → 𝒜 → ℝ}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (hB : 0 ≤ B)
  (hW : ∀ x u, ‖W x u‖ ≤ B)
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms)
  (t : ℕ) :
-- imply
  Integrable (fun ω =>
    W (s[t] ω) (a[t] ω) • ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) (M θ) := by
-- proof
  have hmeas : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s[t] ω, a[t] ω)) :=
    (Measurable.of.All_Eq.snd.fst h₀ t).prodMk (Measurable.of.All_Eq.snd.snd h₀ t)
  have hMsg : ∀ y u, ‖∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ Ms := fun y u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hMs y u
  have hbound : ∀ ω,
    ‖W (s[t] ω) (a[t] ω) • ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))‖ ≤
      B * max Ms 0 := by
    intro ω
    refine (norm_smul_le _ _).trans ?_
    refine mul_le_mul (hW _ _) ((hMsg _ _).trans (le_max_left _ _)) (norm_nonneg _) hB
  refine Integrable.of_bound ?_ (B * max Ms 0) (Filter.Eventually.of_forall hbound)
  exact (StronglyMeasurable.comp_measurable
    (f := fun q : 𝒮 × 𝒜 =>
      W q.1 q.2 • ∇[θ] Real.log (M.policy.prob θ q.1 q.2))
    StronglyMeasurable.of_discrete hmeas).aestronglyMeasurable


/-- Pull a uniformly bounded discounted score series out of the trajectory integral. -/
lemma integral_dot_score_eq_tsum
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ B Ms : ℝ}
  {W : ℕ → 𝒮 → 𝒜 → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (hsP : PSpace (M θ) (AsPathRV.path s))
  (hB : 0 ≤ B)
  (hW : ∀ t x u, ‖W t x u‖ ≤ B)
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms) :
-- imply
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      W t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) =
    ∑' t, γ ^ t • ∫ ω,
      (W t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)))
    ∂(M θ) := by
-- proof
  have : PSpace (M θ) (AsPathRV.path s) := hsP
  have hMsg : ∀ y u, ‖∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ Ms := fun y u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hMs y u
  let F : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → Θ := fun t ω =>
    γ ^ t • (W t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)))
  have hBound : ∀ t ω, ‖F t ω‖ ≤ γ ^ t * (B * max Ms 0) := by
    intro t ω
    calc
      _ = γ ^ t * ‖W t (s[t] ω) (a[t] ω) • ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))‖ := by
        rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t)]
      _ ≤ γ ^ t * (‖W t (s[t] ω) (a[t] ω)‖ * ‖∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))‖) :=
        mul_le_mul_of_nonneg_left (norm_smul_le _ _) (pow_nonneg h₀.1 t)
      _ ≤ γ ^ t * (B * max Ms 0) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hW t (s[t] ω) (a[t] ω))
            ((hMsg _ _).trans (le_max_left _ _)) (norm_nonneg _) hB)
          (pow_nonneg h₀.1 t)
  have hInt : ∀ t, Integrable (F t) (M θ) := by
    intro t
    have hmeas : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s[t] ω, a[t] ω)) :=
      (Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Measurable.of.All_Eq.snd.snd h₁ t)
    refine Integrable.of_bound ?_ (γ ^ t * (B * max Ms 0)) (Filter.Eventually.of_forall (hBound t))
    exact (StronglyMeasurable.comp_measurable
      (f := fun q : 𝒮 × 𝒜 =>
        γ ^ t • (W t q.1 q.2 • ∇[θ] Real.log (M.policy.prob θ q.1 q.2)))
      StronglyMeasurable.of_discrete hmeas).aestronglyMeasurable
  have hSum : Summable fun t => ∫ ω, ‖F t ω‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (B * max Ms 0))
    calc
      _ ≤ ∫ _, γ ^ t * (B * max Ms 0) ∂(M θ) :=
        integral_mono_ae (hInt t).norm (integrable_const _) (Eventually.of_forall (hBound t))
      _ = γ ^ t * (B * max Ms 0) := by
        rw [integral_const]
        simp
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  rw [← integral_tsum_of_summable_integral_norm hInt hSum]
  refine tsum_congr fun t => ?_
  apply integral_smul


/--
Policy gradient with the advantage function (Schulman et al., arXiv 1506.02438, Proposition 1).
With `A = Q - V`,
`∇ 𝔼[(γ ^ id) ⬝ᵥ r] = 𝔼[(γ ^ id) ⬝ᵥ fun t ↦ A(s[t], a[t]) • ∇ log π(a[t] | s[t])]`.
The state-value baseline has policy-score integral zero, so replacing the action value `Q` by the advantage `A` does not change the gradient.

- [action-value policy gradient](?module=Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.All_Eq_Joint.All_EqWithDensity.In_Ico)
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
  {A : Θ → ℕ → 𝒮 → 𝒜 → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (h₂ : ∀ θ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜), Q θ t «\sf{s}»[t] «\sf{a}»[t] = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t] = «\sf{s}»[t] ∧ a[t] = «\sf{a}»[t]))
  (h₃ : ∀ θ t («\sf{s}» : ℕ ⇀ 𝒮), V θ t «\sf{s}»[t] = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t] = «\sf{s}»[t]))
  (h₄ : ∀ θ t x u, A θ t x u = Q θ t x u - V θ t x)
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (h₅ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₆ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₇ : ∀ x, Integrable (g x) μ.measure)
  (h₈ : sup[x] ∫ u, g x u ∂μ.measure < ∞)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : sup[y, u] ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ < ∞) :
-- imply
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ ↦
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      A θ t s[t] a[t] • ∇[θ] Real.log (M.policy.prob θ s[t] a[t])) := by
-- proof
  intro hrP hsP haP
  obtain ⟨Ms, hMsb⟩ := id hMs
  have hMsle : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms :=
    fun y u => hMsb ⟨(y, u), rfl⟩
  have h₂' := fun θ t (sb : ℕ → 𝒮) (ab : ℕ → 𝒜) => h₂ θ t ⟨sb⟩ ⟨ab⟩
  have h₃' := fun θ t (sb : ℕ → 𝒮) => h₃ θ t ⟨sb⟩
  have hQ :=
    GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.All_Eq_Joint.All_EqWithDensity.In_Ico
      (M := M) (θ := θ) (γ := γ) (g := g)
      (Q := Q) (V := V) (r := r) (s := s) (a := a)
      h₀ h₁ h₂' h₃' hπ h₅ h₆ h₇ h₈ hφ hMs
  refine hQ.trans ?_
  have hIntQ := expect_weight_score_eq_integral (W := fun t x u => Q θ t x u) (γ := γ)
    (s := s) (a := a) hsP haP
  have hIntA := expect_weight_score_eq_integral (W := fun t x u => A θ t x u) (γ := γ)
    (s := s) (a := a) hsP haP
  rw [hIntQ, hIntA]
  set B : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hB : 0 ≤ B := mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hpR : Measurable (fun ω t ↦ r[t] ω) :=
    Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG (t : ℕ) : Measurable
    (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ ({ toFun := integ } : Fun ℕ ℝ)[t:]) := by
    unfold Dot.dot Fun.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  have hGbd : ∀ t, ∀ᵐ ω ∂(M θ), ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ B := by
    intro t
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
      (M := M) (r := r.toFun) (s := s.toFun) (a := a.toFun) h₁ θ] with ω hrω
    have hsum : Summable fun k => γ ^ k * |M.env.R| :=
      (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    have hle : ∀ k, ‖γ ^ k * r[t + k] ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      apply mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hrω (t + k))
        (pow_nonneg h₀.1 k)
    have hsn : Summable fun k => ‖γ ^ k * r[t + k] ω‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
    have hG : ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω = ∑' k, γ ^ k * r[t + k] ω := by
      simp [Dot.dot, Function.hPow_apply, id_eq]
    rw [hG]
    calc
      _ ≤ ∑' k, ‖γ ^ k * r[t + k] ω‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, γ ^ k * |M.env.R| := Summable.tsum_le_tsum hle hsn hsum
      _ = B := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
  have hQB_pos (t : ℕ) (x : 𝒮) (u : 𝒜)
    (hpos : (M θ).map (fun ω => (s[t] ω, a[t] ω)) {(x, u)} ≠ 0) :
    ‖Q θ t x u‖ ≤ B := by
    have hsa : Measurable (fun ω => (s[t] ω, a[t] ω)) :=
      (Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Measurable.of.All_Eq.snd.snd h₁ t)
    have h0 : (M θ) ((fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}) ≠ 0 := by
      rwa [← Measure.map_apply hsa (measurableSet_singleton (x, u))]
    have : Q θ t x u =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω
        ∂(M θ)[|(fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}] := by
      rw [h₂ θ t ⟨fun _ => x⟩ ⟨fun _ => u⟩]
      simp only [Expectation.asRV, AsPathRV.path_fun]
      rw [show (s[t], a[t]) = (fun ω => (s[t] ω, a[t] ω)) from rfl]
      rw [Expectation.condEval_eq_integral hpR hsa (hfG t) hpos]
      rfl
    rw [this]
    have hae : ∀ᵐ ω ∂(M θ)[|(fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}],
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ B :=
      cond_absolutelyContinuous.ae_le (hGbd t)
    have : IsProbabilityMeasure
      (M θ)[|(fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}] :=
      cond_isProbabilityMeasure h0
    simpa using
      norm_integral_le_of_norm_le_const
        (μ := (M θ)[|(fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}]) hae
  have hVB_pos (t : ℕ) (x : 𝒮)
    (hpos : (M θ).map s[t] {x} ≠ 0) :
    ‖V θ t x‖ ≤ B := by
    have hs : Measurable (s[t] : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮) :=
      Measurable.of.All_Eq.snd.fst h₁ t
    have h0 : (M θ) (s[t] ⁻¹' {x}) ≠ 0 := by
      rwa [← Measure.map_apply hs (measurableSet_singleton x)]
    have : V θ t x =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω
        ∂(M θ)[|s[t] ⁻¹' {x}] := by
      rw [h₃ θ t ⟨fun _ => x⟩]
      simp only [Expectation.asRV, AsPathRV.path_fun]
      rw [Expectation.condEval_eq_integral hpR hs (hfG t) hpos]
      rfl
    rw [this]
    have hae : ∀ᵐ ω ∂(M θ)[|s[t] ⁻¹' {x}],
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ B :=
      cond_absolutelyContinuous.ae_le (hGbd t)
    have : IsProbabilityMeasure (M θ)[|s[t] ⁻¹' {x}] :=
      cond_isProbabilityMeasure h0
    simpa using
      norm_integral_le_of_norm_le_const
        (μ := (M θ)[|s[t] ⁻¹' {x}]) hae
  have hAB_pos (t : ℕ) (x : 𝒮) (u : 𝒜)
    (hpos : (M θ).map (fun ω => (s[t] ω, a[t] ω)) {(x, u)} ≠ 0) :
    ‖A θ t x u‖ ≤ 2 * B := by
    have hsa : Measurable (fun ω => (s[t] ω, a[t] ω)) :=
      (Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Measurable.of.All_Eq.snd.snd h₁ t)
    have hx : (M θ).map s[t] {x} ≠ 0 := by
      have h0 : (M θ) ((fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}) ≠ 0 := by
        rwa [← Measure.map_apply hsa (measurableSet_singleton (x, u))]
      have hs : Measurable (s[t] : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮) :=
        Measurable.of.All_Eq.snd.fst h₁ t
      have hsub : s[t] ⁻¹' {x} ⊇ (fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)} := by
        intro ω hω
        have : s[t] ω = x ∧ a[t] ω = u := Prod.mk.inj hω
        exact this.1
      exact fun hz =>
        h0 (measure_mono_null hsub
          (by rwa [Measure.map_apply hs (measurableSet_singleton x)] at hz))
    calc
      _ = ‖Q θ t x u - V θ t x‖ := by rw [h₄]
      _ ≤ ‖Q θ t x u‖ + ‖V θ t x‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hQB_pos t x u hpos) (hVB_pos t x hx)
      _ = 2 * B := by ring
  let Q₀ : ℕ → 𝒮 → 𝒜 → ℝ := fun t x u =>
    if (M θ).map (fun ω => (s[t] ω, a[t] ω)) {(x, u)} = 0 then 0 else Q θ t x u
  let A₀ : ℕ → 𝒮 → 𝒜 → ℝ := fun t x u =>
    if (M θ).map (fun ω => (s[t] ω, a[t] ω)) {(x, u)} = 0 then 0 else A θ t x u
  let V₀ : ℕ → 𝒮 → ℝ := fun t x =>
    if (M θ).map s[t] {x} = 0 then 0 else V θ t x
  have hQ0B : ∀ t x u, ‖Q₀ t x u‖ ≤ B := fun t x u => by
    simp only [Q₀]
    split_ifs with h0
    ·
      simp
      apply hB
    · apply hQB_pos t x u h0
  have hA0B : ∀ t x u, ‖A₀ t x u‖ ≤ 2 * B := fun t x u => by
    simp only [A₀]
    split_ifs with h0
    ·
      simp
      linarith [hB]
    · apply hAB_pos t x u h0
  have hV0B : ∀ t x, ‖V₀ t x‖ ≤ B := fun t x => by
    simp only [V₀]
    split_ifs with h0
    ·
      simp
      apply hB
    · apply hVB_pos t x h0
  have h2B : 0 ≤ 2 * B := mul_nonneg (by norm_num) hB
  have hposSA : ∀ t, ∀ᵐ ω ∂(M θ),
    (M θ).map (fun ω => (s[t] ω, a[t] ω)) {(s[t] ω, a[t] ω)} ≠ 0 := by
    intro t
    let pair : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 × 𝒜 := fun ω => (s[t] ω, a[t] ω)
    have hpair : Measurable pair :=
      (Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Measurable.of.All_Eq.snd.snd h₁ t)
    rw [ae_iff]
    have e :
      {ω | ¬(M θ).map pair {pair ω} ≠ 0} =
        ⋃ z ∈ {z : 𝒮 × 𝒜 | (M θ).map pair {z} = 0}, pair ⁻¹' {z} := by
      ext ω
      simp
    rw [e]
    refine (measure_biUnion_null_iff (Set.to_countable _)).2 fun z hz => ?_
    simpa [Measure.map_apply hpair (measurableSet_singleton z)] using hz
  have hposS : ∀ t, ∀ᵐ ω ∂(M θ), (M θ).map s[t] {s[t] ω} ≠ 0 := by
    intro t
    have hs : Measurable (s[t] : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮) :=
      Measurable.of.All_Eq.snd.fst h₁ t
    rw [ae_iff]
    have e :
      {ω | ¬(M θ).map s[t] {s[t] ω} ≠ 0} =
        ⋃ z ∈ {z : 𝒮 | (M θ).map s[t] {z} = 0}, s[t] ⁻¹' {z} := by
      ext ω
      simp
    rw [e]
    refine (measure_biUnion_null_iff (Set.to_countable _)).2 fun z hz => ?_
    simpa [Measure.map_apply hs (measurableSet_singleton z)] using hz
  have hscoreQ : ∀ t, ∀ᵐ ω ∂(M θ),
    Q θ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) =
    Q₀ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) := by
    intro t
    filter_upwards [hposSA t] with ω hpos
    simp [Q₀, hpos]
  have hscoreA : ∀ t, ∀ᵐ ω ∂(M θ),
    A θ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) =
    A₀ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) := by
    intro t
    filter_upwards [hposSA t] with ω hpos
    simp [A₀, hpos]
  have hscoreV : ∀ t, ∀ᵐ ω ∂(M θ),
    V θ t (s[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) =
    V₀ t (s[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) := by
    intro t
    filter_upwards [hposS t] with ω hpos
    simp [V₀, hpos]
  have hIntQ0 :
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      Q θ t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      Q₀ t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hscoreQ] with ω hω
    simp only [Dot.dot, Function.hPow_apply, id_eq, hω]
  have hIntA0 :
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      A θ t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      A₀ t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hscoreA] with ω hω
    simp only [Dot.dot, Function.hPow_apply, id_eq, hω]
  rw [hIntQ0, hIntA0,
    integral_dot_score_eq_tsum (W := Q₀) (B := B) (Ms := Ms)
      (M := M) (θ := θ) (γ := γ) (r := r) (s := s) (a := a) h₀ h₁ hsP hB hQ0B hMsle,
    integral_dot_score_eq_tsum (W := A₀) (B := 2 * B) (Ms := Ms)
      (M := M) (θ := θ) (γ := γ) (r := r) (s := s) (a := a) h₀ h₁ hsP h2B hA0B hMsle]
  have hIntQ0t : ∀ t,
    ∫ ω, (Q₀ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) =
    ∫ ω, (Q θ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) := by
    intro t
    apply (integral_congr_ae (hscoreQ t)).symm
  have hIntA0t : ∀ t,
    ∫ ω, (A₀ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) =
    ∫ ω, (A θ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) := by
    intro t
    apply (integral_congr_ae (hscoreA t)).symm
  simp_rw [hIntQ0t, hIntA0t]
  refine tsum_congr fun t => ?_
  congr 1
  have hintA0 := integrable_weight_score (W := fun x u => A₀ t x u)
    (M := M) (θ := θ) (r := r) (s := s) (a := a) (B := 2 * B) (Ms := Ms)
    h₁ h2B (hA0B t) hMsle t
  have hintV0 := integrable_weight_score (W := fun x u => V₀ t x)
    (M := M) (θ := θ) (r := r) (s := s) (a := a) (B := B) (Ms := Ms)
    h₁ hB (fun x _ => hV0B t x) hMsle t
  have hintA : Integrable (fun ω =>
    A θ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) (M θ) :=
    hintA0.congr ((hscoreA t).mono fun _ h => h.symm)
  have hintV : Integrable (fun ω =>
    V θ t (s[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) (M θ) :=
    hintV0.congr ((hscoreV t).mono fun _ h => h.symm)
  have hV0 :=
    integral_state_score_zero (M := M) (θ := θ) (r := r) (s := s) (a := a)
      (g := g) (C := B) (Ms := Ms) h₁ h₅ h₆ h₇ (V₀ t)
      StronglyMeasurable.of_discrete.measurable (hV0B t) hφ hMsle t
  have hsum : ∀ ω,
    Q θ t (s[t] ω) (a[t] ω) • ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) =
      A θ t (s[t] ω) (a[t] ω) • ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) +
        V θ t (s[t] ω) • ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) := by
    intro ω
    rw [← add_smul]
    congr 1
    rw [h₄]
    ring
  have hVeq : ∫ ω, (V θ t (s[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) = 0 :=
    (integral_congr_ae (hscoreV t)).trans hV0
  rw [integral_congr_ae (Filter.Eventually.of_forall hsum), integral_add hintA hintV, hVeq,
    add_zero]


-- created on 2023-04-13
-- updated on 2026-11-14
