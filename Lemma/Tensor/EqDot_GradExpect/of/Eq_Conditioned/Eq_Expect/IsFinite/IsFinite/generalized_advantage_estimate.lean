import Lemma.Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate
import Lemma.Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded.Discount
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.PSpace.of.Measure.eq.Count.Measurable
import Lemma.Measure.Count.eq.ProdCountS
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.stats.variance
import sympy.stats.cond_expectation
import sympy.stats.policy_trajectory.advantage
import sympy.vector.Basic
import sympy.vector.operators
import sympy.concrete.sup
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology
open scoped ENNReal.ToRealCoe


/--
Generalized advantage estimation (Schulman et al., arXiv 1506.02438): with the temporal-difference residuals
`δ[j] = r[j] + γ * V(s[j+1]) - V(s[j])` and `λ ∈ [0, 1]`, the generalized advantage
`A[t] = (γ * λ) ** Stack[k](k) @ δ[t:]` gives
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[∑' t, γ ^ t • A[t] • ∇ log π(a[t] | s[t])]`.
`λ = 1` is `unbiased_advantage_estimate`.
The proof compares with it: the terms `δ[t + k]`, `k ≥ 1`, have zero expectation against the score
`∇ log π(a[t] | s[t])` of the earlier pair `(s[t], a[t])` (Markov property and Bellman equation for the value
function, `E_delta_psi` in `sympy.stats.policy_trajectory.advantage`), so that for every discount `c ∈ [0, 1)`
`𝔼[((c ** Stack[k](k)) @ δ[t:]) • ∇ log π(a[t] | s[t])] = 𝔼[δ[t] • ∇ log π(a[t] | s[t])]`.
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
  (h₄ : ℓ ∈ Set.Icc 0 1) :
-- imply
  have : ∀ θ t, SinglePSpace (M.traj θ) (JointRandomSymbol (a t) (s t)) := fun _ t =>
    Random.PSpace.of.Measure.eq.Count.Measurable ((a_meas t).prodMk (s_meas t)) (by
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
        (((fun k : ℕ => (γ * ℓ) ^ k) @ (fun k : ℕ => r (t + k) + γ * V θ (t + k + 1) (s (t + k + 1)) - V θ (t + k) (s (t + k)))) •
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
  have hc : γ * ℓ ∈ Set.Ico 0 1 :=
    ⟨mul_nonneg h₀.1 h₄.1, (mul_le_of_le_one_right h₀.1 h₄.2).trans_lt h₀.2⟩
  have hscore : ∀ t, ∀ᵐ ω ∂(M.traj θ),
      fderiv ℝ (fun θ' => (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [reach_ae M θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M.traj θ').real (s t ⁻¹' {s t ω})) θ :=
      (P_diff M h₂ h₇ t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [Random.ProbCond.eq.OfRealPol.of.Ne_0 hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
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
  have hbd : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ᵐ ω ∂(M.traj θ), ∀ t,
      ‖∑' k, c ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))‖ ≤
        (1 - c)⁻¹ * M.deltaBound γ := by
    intro c hc'
    filter_upwards [delta_sum_bdd M θ h₀ hc', hδ] with ω h1 h2 t
    have e : ∑' k, c ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω)) =
        ∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) - M.Vc θ γ (s (t + k) ω)) :=
      tsum_congr fun k => by rw [h2 (t + k)]
    rw [e]
    exact h1 t
  -- the `c`-discounted advantage against the score only sees the first residual
  have hinner : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ t, ∫ ω,
      (∑' k, c ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))) •
        fderiv ℝ (fun θ' => (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M.traj θ) =
      ∫ ω, (r t ω + γ * M.Vc θ γ (s (t + 1) ω) - M.Vc θ γ (s t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) := by
    intro c hc' t
    refine (integral_congr_ae ?_).trans
      (E_sum_delta M θ h₀ hc' t (fun y u => fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ))
    filter_upwards [hscore t, hδ] with ω h1 h2
    rw [h1]
    beta_reduce
    congr 1
    exact tsum_congr fun k => by rw [h2 (t + k)]
  have hmeas : ∀ k, Measurable fun ω : ℕ → S × A × ℝ =>
      (fun (s : ℕ → S) (_ : ℕ → A) (r : ℕ → ℝ) (k : ℕ) => r k + γ * V θ (k + 1) (s (k + 1)) - V θ k (s k))
        (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k := fun k =>
    ((r_meas k).add (((measurable_of_countable (V θ (k + 1))).comp (s_meas (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (V θ k)).comp (s_meas k))
  have hbase : ∇[θ] (
      have : PSpace (M.traj θ) (AsPathRV.path (r (S := S) (A := A))) :=
        PSpace.of_process_path (fun t => ⟨(r_meas t).aemeasurable⟩)
      𝔼[r: M.traj θ](((fun t : ℕ => γ ^ t) @ r))) =
      𝔼[s, a, r : M.traj θ](
        ∑' t, γ ^ t •
          (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => r (t + k) + γ * V θ (t + k + 1) (s (t + k + 1)) - V θ (t + k) (s (t + k)))) •
            ∇[θ] (ℙ[M.traj θ]((PolicyGradient.a t) = a t | (PolicyGradient.s t) = s t) : ℝ).log)) :=
    Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate
      h₀ hS hA h₁ h₂ h₃o
  have hA₁ := Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded.Discount
    (X := fun s _ r k => r k + γ * V θ (k + 1) (s (k + 1)) - V θ k (s k)) (c := γ)
    h₀ hS hA hmeas (hbd γ h₀) h₂ h₃o
  have hA₂ := Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded.Discount
    (X := fun s _ r k => r k + γ * V θ (k + 1) (s (k + 1)) - V θ k (s k)) (c := γ * ℓ)
    h₀ hS hA hmeas (hbd (γ * ℓ) hc) h₂ h₃o
  have e : ∑' t, γ ^ t • ∫ ω,
      (∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))) •
        fderiv ℝ (fun θ' => (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M.traj θ) =
      ∑' t, γ ^ t • ∫ ω,
      (∑' k, (γ * ℓ) ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))) •
        fderiv ℝ (fun θ' => (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M.traj θ) :=
    tsum_congr fun t => by rw [hinner γ h₀ t, hinner (γ * ℓ) hc t]
  exact hbase.trans (hA₁.symm.trans ((congrArg (InnerProductSpace.toDual ℝ Θ).symm e).trans hA₂))


-- created on 2026-10-01
