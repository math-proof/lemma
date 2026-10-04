import Lemma.Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.generalized_advantage_estimate
import Lemma.Tensor.EqDot.of.IsFinite.generalized_advantage_estimate
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Measure.Count.eq.ProdCountS
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.stats.variance
import sympy.stats.cond_expectation
import sympy.stats.policy_trajectory.advantage
import sympy.vector.Basic
import sympy.vector.operators
import sympy.concrete.sup
open scoped ENNReal.ToRealCoe
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology


/--
Generalized advantage estimation with the paper's weighted-average estimator (Schulman et al., arXiv 1506.02438, Eq. (16)):
with the temporal-difference residuals `δ[j] = r[j] + γ * V(s[j+1]) - V(s[j])` and `λ ∈ [0, 1)`, the
exponentially weighted average of the `(k + 1)`-step advantage estimates
`A[t] = (1 - λ) * ∑' k, λ ^ k * ∑ i ∈ range (k + 1), γ ^ i * δ[t + i]` gives
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[∑' t, γ ^ t • A[t] • ∇ log π(a[t] | s[t])]`.
The proof rewrites `A[t]` pointwise into the closed form `(γ * λ) ** Stack[k](k) @ δ[t:]`
(`Tensor.EqDot.of.IsFinite.generalized_advantage_estimate`, the residuals being almost surely bounded since
`V` is the value function, `delta_ae_bdd` in `sympy.stats.policy_trajectory.advantage`) and applies
`Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.generalized_advantage_estimate`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ ℓ : ℝ}
  {V : Θ → ℕ → S → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₁ : ∀ θ t x, ((M.traj θ) (s t ⁻¹' {x}) ≠ 0) →
    V θ t x = 𝔼[r : M.traj θ](∑' k, γ ^ k * r (t + k) | s t = x))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₄ : ℓ ∈ Set.Ico 0 1) :
-- imply
  have : ∀ θ t, SinglePSpace (M.traj θ) (JointRandomSymbol (a t) (s t)) := fun _ t =>
    Random.SinglePSpace.of.EqMeasureCount.Measurable ((a_meas t).prodMk (s_meas t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [hA, hS, Measure.Count.eq.ProdCountS])
  have hs : ∀ t, PSpace (M.traj θ) (s (S := S) (A := A) t) := fun t =>
    ⟨(s_meas t).aemeasurable⟩
  have ha : ∀ t, PSpace (M.traj θ) (a (S := S) (A := A) t) := fun t =>
    ⟨(a_meas t).aemeasurable⟩
  have hr : ∀ t, PSpace (M.traj θ) (r (S := S) (A := A) t) := fun t =>
    ⟨(r_meas t).aemeasurable⟩
  have : PSpace (M.traj θ) (AsPathRV.path (s (S := S) (A := A))) :=
    PSpace.of_process_path hs
  have : PSpace (M.traj θ) (AsPathRV.path (a (S := S) (A := A))) :=
    PSpace.of_process_path ha
  have : PSpace (M.traj θ) (AsPathRV.path (r (S := S) (A := A))) :=
    PSpace.of_process_path hr
  let : MeasurableSpace Θ := borel Θ
  have : BorelSpace Θ := ⟨rfl⟩
  ∇[θ] (
    have : PSpace (M.traj θ) (AsPathRV.path (r (S := S) (A := A))) :=
      PSpace.of_process_path (fun t => ⟨(r_meas t).aemeasurable⟩)
    𝔼[r: M.traj θ](((fun t : ℕ => γ ^ t) @ r))) =
    𝔼[s, a, r : M.traj θ](
      ∑' t, γ ^ t •
        (((1 - ℓ) * ∑' k, ℓ ^ k * ∑ i ∈ Finset.range (k + 1), γ ^ i *
            (r (t + i) + γ * V θ (t + i + 1) (s (t + i + 1)) - V θ (t + i) (s (t + i)))) •
          ∇[θ] (ℙ[M.traj θ]((PolicyGradient.a t) = a t | (PolicyGradient.s t) = s t) : ℝ).log)) := by
-- proof
  intro hP _hs _ha _hr _hps _hpa _hpr
  classical
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have h₃o := h₃
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₃
  obtain ⟨C, hC⟩ := id h₃
  have h₇ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  have hℓ : ℓ ∈ Set.Icc 0 1 := ⟨h₄.1, h₄.2.le⟩
  have hpR : Measurable (fun ω t ↦ r (S := S) (A := A) t ω) := measurable_pi_lambda _ fun t => r_meas t
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ ∑' k, γ ^ k * integ (t + k)) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hVr : ∀ θ' t x, ((M.traj θ').real (s t ⁻¹' {x}) ≠ 0) → (V θ' t x = M.V θ' γ t x) := fun θ' t x hp => by
    have hp' : (M.traj θ') (s t ⁻¹' {x}) ≠ 0 := fun h0 =>
      hp ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 h0)
    rw [h₁ θ' t x hp']
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t), M.V_eq_integral θ' γ t x]
    rfl
  -- almost surely the learned value is the time-free value function
  have hVc : ∀ᵐ ω ∂(M.traj θ), ∀ k, V θ k (s k ω) = M.Vc θ γ (s k ω) :=
    (reach_ae M θ).mono fun ω h k => (hVr θ k _ (h k)).trans (V_eq_Vc M θ h₀ k _ (h k))
  have hδ : ∀ᵐ ω ∂(M.traj θ), ∀ j, r j ω + γ * V θ (j + 1) (s (j + 1) ω) - V θ j (s j ω) =
      r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω) :=
    hVc.mono fun ω h j => by rw [h j, h (j + 1)]
  -- almost surely the residuals are bounded
  have hbdd : ∀ᵐ ω ∂(M.traj θ),
      BddAbove (Set.range fun j => |r j ω + γ * V θ (j + 1) (s (j + 1) ω) - V θ j (s j ω)|) := by
    filter_upwards [delta_ae_bdd M θ h₀, hδ] with ω h1 h2
    refine ⟨M.deltaBound γ, ?_⟩
    rintro _ ⟨j, rfl⟩
    have := h1 j
    rw [Real.norm_eq_abs] at this
    beta_reduce
    rw [h2 j]
    exact this
  -- almost surely the paper's estimator is the closed form
  have hpt : ∀ᵐ ω ∂(M.traj θ), ∀ t,
      (1 - ℓ) * ∑' k, ℓ ^ k * ∑ i ∈ Finset.range (k + 1), γ ^ i *
        (r (t + i) ω + γ * V θ (t + i + 1) (s (t + i + 1) ω) - V θ (t + i) (s (t + i) ω)) =
      (fun k : ℕ => (γ * ℓ) ^ k) @
        (fun k : ℕ => r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω)) := by
    filter_upwards [hbdd] with ω hb t
    exact Tensor.EqDot.of.IsFinite.generalized_advantage_estimate
      (δ := fun j => r j ω + γ * V θ (j + 1) (s (j + 1) ω) - V θ j (s j ω)) (t := t) hb h₀ h₄
  have hmeas : ∀ k, Measurable fun ω : ℕ → S × A × ℝ =>
      r k ω + γ * V θ (k + 1) (s (k + 1) ω) - V θ k (s k ω) := fun k =>
    ((r_meas k).add (((measurable_of_countable (V θ (k + 1))).comp (s_meas (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (V θ k)).comp (s_meas k))
  -- the expectation of a pathwise functional is a Bochner integral
  have hexp : ∀ F : ℕ → (ℕ → S) → (ℕ → A) → (ℕ → ℝ) → ℝ,
      (∀ t, Measurable fun ω : ℕ → S × A × ℝ => F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω)) →
      𝔼[s, a, r : M.traj θ](
        ∑' t, γ ^ t • (F t s a r •
          ∇[θ] (ℙ[M.traj θ]((PolicyGradient.a t) = a t | (PolicyGradient.s t) = s t) : ℝ).log)) =
      ∫ ω, ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
        ∇[θ] (ℙ[M.traj θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) ∂(M.traj θ) := by
    intro F hF
    have hg := fun t : ℕ =>
      StronglyMeasurable.smul (hF t).stronglyMeasurable
        ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
          gradient (fun θ' => (ℙ[M.traj θ']((a t) = p.2 | (s t) = p.1) : ℝ).log) θ)).comp_measurable
            ((s_meas t).prodMk (a_meas t)))
    have hGsm : StronglyMeasurable fun ω : ℕ → S × A × ℝ =>
        ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
          ∇[θ] (ℙ[M.traj θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) :=
      StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
        (hg t).const_smul (γ ^ t)
    let fromPath := fun (p : (ℕ → S) × (ℕ → A) × (ℕ → ℝ)) =>
      fun t => (p.1 t, p.2.1 t, p.2.2 t)
    have fromPath_meas : Measurable fromPath :=
      measurable_pi_lambda _ fun t =>
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          ((((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
            ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))))
    have hx : AEMeasurable
        (JointRandomSymbol (AsPathRV.path s)
          (JointRandomSymbol (AsPathRV.path a) (AsPathRV.path r))) (M.traj θ) :=
      PSpace.aemeasurable
    simp only [AsPathRV.path_process]
    rw [Expectation.ofRV, expectation_bochner]
    refine (integral_map hx ?_).trans ?_
    · exact (hGsm.comp_measurable fromPath_meas).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun p => by
          simp only [Function.comp_apply, fromPath]
          rfl)
    simp only [AsPathRV.path_process, JointRandomSymbol]
  have hF₁ : ∀ t, Measurable fun ω : ℕ → S × A × ℝ =>
      (1 - ℓ) * ∑' k, ℓ ^ k * ∑ i ∈ Finset.range (k + 1), γ ^ i *
        (r (t + i) ω + γ * V θ (t + i + 1) (s (t + i + 1) ω) - V θ (t + i) (s (t + i) ω)) := fun t =>
    (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
      (Finset.measurable_sum _ fun i _ => (hmeas (t + i)).const_mul _).const_mul _).const_mul _
  have hF₂ : ∀ t, Measurable fun ω : ℕ → S × A × ℝ =>
      ((fun k : ℕ => (γ * ℓ) ^ k) @
        (fun k : ℕ => r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))) := fun t => by
    show Measurable fun ω : ℕ → S × A × ℝ => ∑' k, (γ * ℓ) ^ k *
      (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))
    exact Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k => (hmeas (t + k)).const_mul _
  have e := (hexp (fun t s a r => (1 - ℓ) * ∑' k, ℓ ^ k * ∑ i ∈ Finset.range (k + 1), γ ^ i *
        (r (t + i) + γ * V θ (t + i + 1) (s (t + i + 1)) - V θ (t + i) (s (t + i)))) hF₁).trans
    ((integral_congr_ae (by
      filter_upwards [hpt] with ω h
      refine tsum_congr fun t => ?_
      beta_reduce
      rw [h t])).trans
      (hexp (fun t s a r => (fun k : ℕ => (γ * ℓ) ^ k) @
        (fun k : ℕ => r (t + k) + γ * V θ (t + k + 1) (s (t + k + 1)) - V θ (t + k) (s (t + k)))) hF₂).symm)
  exact (Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.generalized_advantage_estimate
    (θ := θ) h₀ hS hA h₁ h₂ h₃o hℓ).trans e.symm


-- created on 2026-10-01
