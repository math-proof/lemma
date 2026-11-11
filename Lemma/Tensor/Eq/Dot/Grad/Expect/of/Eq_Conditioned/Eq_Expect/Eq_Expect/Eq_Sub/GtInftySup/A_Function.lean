import Notation.Fun
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico
import Lemma.Random.Integral.eq.Sum_Sum_SMul
import Lemma.Random.NormQ.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.NormV.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.SumSMulProbFderiv_FunLog_Prob.eq.Zero.of.All_AllDifferentiable_FunProbPol
import Instance.Data.Vector.Basic.Dot
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 800000


/-- Discounted score expectation equals the observation integral. -/
lemma expect_weight_score_eq_integral
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
  {M : Model Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {W : ℕ → 𝒮 → 𝒜 → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (hP : ∀ θ t, SinglePSpace (M θ) (a[t], s[t]))
  (hsP : PSpace (M θ) (AsPathRV.path s))
  (haP : PSpace (M θ) (AsPathRV.path a)) :
-- imply
  𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      W t s[t] a[t] • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      W t (s[t] ω) (a[t] ω) •
        ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log) ∂(M θ) := by
-- proof
  have : ∀ θ t, SinglePSpace (M θ) (a[t], s[t]) := hP
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
        γ ^ t • W t q.1 q.2 • ∇[θ] (ℙ[M θ](a[t] = q.2 | s[t] = q.1) : ℝ).log)
      StronglyMeasurable.of_discrete
      (show Measurable fun p : (ℕ → 𝒮) × (ℕ → 𝒜) ↦ (p.1 t, p.2 t) from
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          ((measurable_pi_apply t).comp measurable_snd))
  ·
    simp only [JointRandomSymbol, AsPathRV.path_fun, Dot.dot, Function.hPow_apply, id_eq]


/-- Almost everywhere, the conditional-probability score is the policy score. -/
lemma gradLog_ae
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜}
  {θ : Θ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₂ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (hP : ∀ θ t, SinglePSpace (M θ) (a[t], s[t]))
  (t : ℕ) :
-- imply
  ∀ᵐ ω ∂(M θ),
    ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log =
      ∇[θ] (Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) := by
-- proof
  filter_upwards [AeRealPreimageSS.ne.Zero (s := s.toFun) (M := M) θ] with ω hω
  have hc : ContinuousAt (fun θ' => (M θ').real (s[t] ⁻¹' {s[t] ω})) θ :=
    (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ t (s[t] ω) θ).continuousAt
  have hfd :
    fderiv ℝ (fun θ' => (ℙ[M θ'](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log) θ =
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s[t] ω) (a[t] ω))) θ := by
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' hne => ?_)
    have hprob := ProbCond.eq.OfRealPol.of.Ne_0 (M := M) (θ := θ') (t := t)
      (x := s[t] ω) (u := a[t] ω) h₀ (hP θ' t) hne
    beta_reduce
    rw [hprob, ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  simp only [gradient]
  exact congrArg (InnerProductSpace.toDual ℝ Θ).symm hfd


/-- A state-dependent baseline has conditional score zero, so it drops out of the gradient. -/
private lemma integral_state_score_zero
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜}
  {θ : Θ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₂ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (hP : ∀ θ t, SinglePSpace (M θ) (a[t], s[t]))
  (h : 𝒮 → ℝ)
  (t : ℕ) :
-- imply
  ∫ ω, h (s[t] ω) •
      ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log
    ∂(M θ) = 0 := by
-- proof
  have hAe : ∀ᵐ ω ∂(M θ),
      ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log =
        ∇[θ] (Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) :=
    gradLog_ae (M := M) (θ := θ) (r := r) (s := s) (a := a) h₀ h₁ h₂ hP t
  have hPol : ∫ ω,
      (h (s[t] ω) • ∇[θ] (Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))))
    ∂(M θ) = 0 := by
    rw [Integral.eq.Sum_Sum_SMul (M := M) h₀ θ t
      (fun y u => h y • ∇[θ] (Real.log (M.policy.prob θ y u)))]
    refine Finset.sum_eq_zero fun y _ => ?_
    let e := (InnerProductSpace.toDual ℝ Θ).symm
    have hsm : ∀ u, ((M θ).real (s[t] ⁻¹' {y}) * M.policy.prob θ y u) •
        (h y • ∇[θ] (Real.log (M.policy.prob θ y u))) =
        ((M θ).real (s[t] ⁻¹' {y}) * h y) •
          e (M.policy.prob θ y u • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) := fun u => by
      rw [smul_smul, mul_right_comm, ← smul_smul]
      simp [e, gradient, map_smul]
    simp_rw [hsm, ← Finset.smul_sum]
    rw [← map_sum e (fun u => M.policy.prob θ y u • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) Finset.univ]
    rw [SumSMulProbFderiv_FunLog_Prob.eq.Zero.of.All_AllDifferentiable_FunProbPol (M := M) h₁ θ y]
    simp
  refine (integral_congr_ae ?_).trans hPol
  filter_upwards [hAe] with ω hω
  rw [hω]


/-- One time step of a score, weighted by a real function of the visited state and action, is integrable. -/
lemma integrable_weight_score
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜}
  {θ : Θ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {W : 𝒮 → 𝒜 → ℝ}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (hP : ∀ θ t, SinglePSpace (M θ) (a[t], s[t]))
  (t : ℕ) :
-- imply
  Integrable (fun ω =>
    W (s[t] ω) (a[t] ω) • ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log) (M θ) := by
-- proof
  have hmeas : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s[t] ω, a[t] ω)) :=
    (Measurable.of.All_Eq.snd.fst h₀ t).prodMk (Measurable.of.All_Eq.snd.snd h₀ t)
  let φ := fun (z : 𝒮 × 𝒜) =>
    ‖W z.1 z.2 • ∇[θ] (ℙ[M θ](a[t] = z.2 | s[t] = z.1) : ℝ).log‖
  have hφ : ∀ z, 0 ≤ φ z := fun _ => norm_nonneg _
  let C := (∑ z, φ z) + 1
  have hC : ∀ z, φ z ≤ C := by
    intro z
    have : φ z ≤ ∑ z, φ z := Finset.single_le_sum (fun z _ => hφ z) (Finset.mem_univ z)
    linarith
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun ω => hC (s[t] ω, a[t] ω))
  exact (StronglyMeasurable.comp_measurable
    (f := fun q : 𝒮 × 𝒜 =>
      W q.1 q.2 • ∇[θ] (ℙ[M θ](a[t] = q.2 | s[t] = q.1) : ℝ).log)
    StronglyMeasurable.of_discrete hmeas).aestronglyMeasurable


/-- Pull a uniformly bounded discounted score series out of the trajectory integral. -/
lemma integral_dot_score_eq_tsum
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜}
  {θ : Θ}
  {γ B : ℝ}
  {W : ℕ → 𝒮 → 𝒜 → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (hP : ∀ θ t, SinglePSpace (M θ) (a[t], s[t]))
  (hsP : PSpace (M θ) (AsPathRV.path s))
  (hB : 0 ≤ B)
  (hW : ∀ t x u, ‖W t x u‖ ≤ B) :
-- imply
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      W t (s[t] ω) (a[t] ω) •
        ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log) ∂(M θ) =
    ∑' t, γ ^ t • ∫ ω,
      W t (s[t] ω) (a[t] ω) •
        ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log
    ∂(M θ) := by
-- proof
  have : PSpace (M θ) (AsPathRV.path s) := hsP
  have hMsEx : ∃ Ms, 0 ≤ Ms ∧ ∀ x u, ‖∇[θ] (Real.log (M.policy.prob θ x u))‖ ≤ Ms := by
    let φ := fun (z : 𝒮 × 𝒜) => ‖∇[θ] (Real.log (M.policy.prob θ z.1 z.2))‖
    have hφ : ∀ z, 0 ≤ φ z := fun _ => norm_nonneg _
    refine ⟨(∑ z, φ z) + 1, ?_, fun x u => ?_⟩
    ·
      have : 0 ≤ ∑ z, φ z := Finset.sum_nonneg fun z _ => hφ z
      linarith
    ·
      have hle : φ (x, u) ≤ ∑ z, φ z :=
        Finset.single_le_sum (fun z _ => hφ z) (Finset.mem_univ (x, u))
      linarith
  obtain ⟨Ms, _, hMs⟩ := hMsEx
  have hscore : ∀ᵐ ω ∂(M θ), ∀ t,
      ‖∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log‖ ≤ Ms := by
    have ht : ∀ t, ∀ᵐ ω ∂(M θ),
        ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log =
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) :=
      fun t => gradLog_ae (M := M) (θ := θ) (r := r) (s := s) (a := a) h₁ h₂ h₃ hP t
    filter_upwards [ae_all_iff.2 ht] with ω hω
    intro t
    rw [hω t]
    exact hMs (s[t] ω) (a[t] ω)
  let F : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → Θ := fun t ω =>
    γ ^ t • (W t (s[t] ω) (a[t] ω) •
      ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log)
  have hBound : ∀ t, ∀ᵐ ω ∂(M θ), ‖F t ω‖ ≤ γ ^ t * (B * Ms) := by
    intro t
    filter_upwards [hscore] with ω hω
    calc
      _ = γ ^ t * ‖W t (s[t] ω) (a[t] ω) • ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log‖ := by
        rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t)]
      _ ≤ γ ^ t * (‖W t (s[t] ω) (a[t] ω)‖ * ‖∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log‖) :=
        mul_le_mul_of_nonneg_left (norm_smul_le _ _) (pow_nonneg h₀.1 t)
      _ ≤ γ ^ t * (B * Ms) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hW t (s[t] ω) (a[t] ω)) (hω t) (norm_nonneg _) hB) (pow_nonneg h₀.1 t)
  have hInt : ∀ t, Integrable (F t) (M θ) := by
    intro t
    have hmeas : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s[t] ω, a[t] ω)) :=
      (Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Measurable.of.All_Eq.snd.snd h₁ t)
    refine Integrable.of_bound ?_ (γ ^ t * (B * Ms)) (hBound t)
    exact (StronglyMeasurable.comp_measurable
      (f := fun q : 𝒮 × 𝒜 =>
        γ ^ t • (W t q.1 q.2 • ∇[θ] (ℙ[M θ](a[t] = q.2 | s[t] = q.1) : ℝ).log))
      StronglyMeasurable.of_discrete hmeas).aestronglyMeasurable
  have hSum : Summable fun t => ∫ ω, ‖F t ω‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (B * Ms))
    calc
      _ ≤ ∫ _, γ ^ t * (B * Ms) ∂(M θ) :=
        integral_mono_ae (hInt t).norm (integrable_const _) (hBound t)
      _ = γ ^ t * (B * Ms) := by
        rw [integral_const]
        simp
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  rw [← integral_tsum_of_summable_integral_norm hInt hSum]
  refine tsum_congr fun t => ?_
  exact integral_smul (γ ^ t) _


/--
Policy gradient with the advantage function (Schulman et al., arXiv 1506.02438, Proposition 1).
With `A = Q - V`,
`∇ 𝔼[(γ ^ id) ⬝ᵥ r] = 𝔼[(γ ^ id) ⬝ᵥ fun t ↦ A(s[t], a[t]) • ∇ log π(a[t] | s[t])]`.
The state-value baseline has conditional score zero, so replacing the action value `Q` by the advantage `A` does not change the gradient.

- [action-value policy gradient](?module=Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
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
  (h₅ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₆ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a[t], s[t]) := fun _ t =>
    SinglePSpace.of.Measurable.Measurable
      (Measurable.of.All_Eq.snd.snd h₁ t)
      (Measurable.of.All_Eq.snd.fst h₁ t)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ ↦
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      A θ t s[t] a[t] • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
-- proof
  intro hSP hsP haP hrP
  have h₂' := fun θ t (sb : ℕ → 𝒮) (ab : ℕ → 𝒜) => h₂ θ t ⟨sb⟩ ⟨ab⟩
  have h₃' := fun θ t (sb : ℕ → 𝒮) => h₃ θ t ⟨sb⟩
  have hQ :=
    GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico
      (M := M) (θ := θ) (γ := γ) (Q := Q) (V := V) (r := r.toFun) (s := s.toFun) (a := a.toFun) h₀ h₁ h₂' h₃' h₅ h₆
  refine hQ.trans ?_
  have hIntQ := expect_weight_score_eq_integral (W := fun t x u => Q θ t x u) (γ := γ) (s := s) (a := a) hSP hsP haP
  have hIntA := expect_weight_score_eq_integral (W := fun t x u => A θ t x u) (γ := γ) (s := s) (a := a) hSP hsP haP
  let s' := s.toFun
  let a' := a.toFun
  have hsame :
    𝔼[s', a' : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      Q θ t (s' t) (a' t) • ∇[θ] (ℙ[M θ](a' t | s' t) : ℝ).log) =
      𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        Q θ t s[t] a[t] • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
    rfl
  rw [hsame, hIntQ, hIntA]
  set B : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hB : 0 ≤ B := mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hQB : ∀ t x u, ‖Q θ t x u‖ ≤ B := by
    intro t x u
    rw [h₂ θ t ⟨fun _ => x⟩ ⟨fun _ => u⟩]
    exact NormQ.le.MulSub1Abs_R.of.In_Ico (M := M) (γ := γ) (r := r.toFun) (s := s.toFun) (a := a.toFun) h₀ h₁ θ t x u
  have hVB : ∀ t x, ‖V θ t x‖ ≤ B := by
    intro t x
    rw [h₃ θ t ⟨fun _ => x⟩]
    exact NormV.le.MulSub1Abs_R.of.In_Ico (M := M) (γ := γ) (r := r.toFun) (s := s.toFun) (a := a.toFun) h₀ h₁ θ t x
  have hAB : ∀ t x u, ‖A θ t x u‖ ≤ 2 * B := by
    intro t x u
    calc
      _ = ‖Q θ t x u - V θ t x‖ := by rw [h₄]
      _ ≤ ‖Q θ t x u‖ + ‖V θ t x‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hQB t x u) (hVB t x)
      _ = 2 * B := by ring
  have h2B : 0 ≤ 2 * B := mul_nonneg (by norm_num) hB
  rw [integral_dot_score_eq_tsum (W := fun t x u => Q θ t x u) (B := B)
      (M := M) (θ := θ) (γ := γ) (r := r) (s := s) (a := a) h₀ h₁ h₅ h₆ hSP hsP hB hQB,
    integral_dot_score_eq_tsum (W := fun t x u => A θ t x u) (B := 2 * B)
      (M := M) (θ := θ) (γ := γ) (r := r) (s := s) (a := a) h₀ h₁ h₅ h₆ hSP hsP h2B hAB]
  refine tsum_congr fun t => ?_
  congr 1
  have hintA := integrable_weight_score (W := fun x u => A θ t x u) (M := M) (θ := θ) (r := r) (s := s) (a := a) h₁ hSP t
  have hintV := integrable_weight_score (W := fun x u => V θ t x) (M := M) (θ := θ) (r := r) (s := s) (a := a) h₁ hSP t
  have hV0 := integral_state_score_zero (M := M) (θ := θ) (r := r) (s := s) (a := a) h₁ h₅ h₆ hSP (fun x => V θ t x) t
  have hsum : ∀ ω,
      Q θ t (s[t] ω) (a[t] ω) • ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log =
        A θ t (s[t] ω) (a[t] ω) • ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log +
          V θ t (s[t] ω) • ∇[θ] (ℙ[M θ](a[t] = (a[t] ω) | s[t] = (s[t] ω)) : ℝ).log := by
    intro ω
    rw [← add_smul]
    congr 1
    rw [h₄]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsum), integral_add hintA hintV, hV0, add_zero]


-- created on 2023-04-04
-- updated on 2026-11-11
