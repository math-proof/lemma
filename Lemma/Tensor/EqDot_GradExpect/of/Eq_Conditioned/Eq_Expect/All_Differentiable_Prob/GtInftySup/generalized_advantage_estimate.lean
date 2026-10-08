import Lemma.Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.All_Differentiable_Prob.GtInftySup.unbiased_advantage_estimate
import Lemma.Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded.Discount
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
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.Measurable_R
import Lemma.Random.AeAll_LeNorm_TSum_MulPowSubAddRMul_VcVcMulSub1DeltaBound.of.In_Ico.In_Ico
import Lemma.Random.Integral_SMul.eq.Zero.of.Le.In_Ico
import Lemma.Random.Integral_SMul.of.In_Ico.In_Ico
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random
open scoped ENNReal.ToRealCoe


/--
Generalized advantage estimation (Schulman et al., arXiv 1506.02438): with the temporal-difference residuals
`δ[j] = r[j] + γ * V(s[j+1]) - V(s[j])` and `λ ∈ [0, 1]`, the generalized advantage
`A[t] = (γ * λ) ** Stack[k](k) @ δ[t:]` gives
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[∑' t, γ ^ t • A[t] • ∇ log π(a[t] | s[t])]`.
`λ = 1` is `unbiased_advantage_estimate`.
The proof compares with it: the terms `δ[t + k]`, `k ≥ 1`, have zero expectation against the score
`∇ log π(a[t] | s[t])` of the earlier pair `(s[t], a[t])` (Markov property and Bellman equation for the value
function, `Random.Integral_SMul.eq.Zero.of.Le.In_Ico` in `sympy.stats.policy_trajectory.advantage`), so that for every discount `c ∈ [0, 1)`
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
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₂ : ∀ θ t x, ((M θ) (s t ⁻¹' {x}) ≠ 0) →
    V θ t x = 𝔼[r : M θ](∑' k, γ ^ k * r (t + k) | s t = x))
  (h₃ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₄ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₅ : ℓ ∈ Set.Icc 0 1) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (JointRandomSymbol (a t) (s t)) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable_A h₁ t).prodMk (Random.Measurable_S h₁ t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [hA, hS, Measure.Count.eq.ProdCountS])
  have hs : ∀ t, PSpace (M θ) (s t) := fun t =>
    ⟨(Random.Measurable_S h₁ t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (a t) := fun t =>
    ⟨(Random.Measurable_A h₁ t).aemeasurable⟩
  have hr : ∀ t, PSpace (M θ) (r t) := fun t =>
    ⟨(Random.Measurable_R h₁ t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path (s)) :=
    PSpace.of_process_path hs
  have : PSpace (M θ) (AsPathRV.path (a)) :=
    PSpace.of_process_path ha
  have : PSpace (M θ) (AsPathRV.path (r)) :=
    PSpace.of_process_path hr
  let : MeasurableSpace Θ := borel Θ
  have : BorelSpace Θ := ⟨rfl⟩
  ∇[θ] (
    have : PSpace (M θ) (AsPathRV.path (r)) :=
      PSpace.of_process_path (fun t => ⟨(Random.Measurable_R h₁ t).aemeasurable⟩)
    𝔼[r: M θ](((fun t : ℕ => γ ^ t) @ r))) =
    -- TODO(sympy 𝔼 patch): 𝔽((a₀ t) = … | (s₀ t) = …) with let a₀ := a; let s₀ := s
    let a₀ := a
    let s₀ := s
    𝔼[s, a, r : M θ](
      ∑' t, γ ^ t •
        (((fun k : ℕ => (γ * ℓ) ^ k) @ (fun k : ℕ => r (t + k) + γ * V θ (t + k + 1) (s (t + k + 1)) - V θ (t + k) (s (t + k)))) •
          ∇[θ] (ℙ[M θ]((a₀ t) = (a t) | (s₀ t) = (s t)) : ℝ).log)) := by
-- proof
  intro hP _ _ _ _ _ _
  classical
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have hc : γ * ℓ ∈ Set.Ico 0 1 :=
    ⟨mul_nonneg h₀.1 h₅.1, (mul_le_of_le_one_right h₀.1 h₅.2).trans_lt h₀.2⟩
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₃ h₄ t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
  have hpR : Measurable (fun ω t ↦ r t ω) := measurable_pi_lambda _ fun t => Random.Measurable_R h₁ t
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ ∑' k, γ ^ k * integ (t + k)) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hVr : ∀ θ' t x, ((M θ').real (s t ⁻¹' {x}) ≠ 0) → (V θ' t x = M.V r s θ' γ t x) := fun θ' t x hp => by
    have hp' : (M θ') (s t ⁻¹' {x}) ≠ 0 := fun h0 =>
      hp ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 h0)
    rw [h₂ θ' t x hp']
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t), M.V_eq_integral r s θ' γ t x]
    rfl
  -- almost surely the learned value is the time-free value function
  have hVc : ∀ᵐ ω ∂(M θ), ∀ k, V θ k (s k ω) = M.Vc θ γ (s k ω) :=
    (AeRealPreimageSS.ne.Zero (s := s) (M := M) θ).mono fun ω h k => (hVr θ k _ (h k)).trans (Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico (M := M) h₀ h₁ θ k _ (h k))
  have hδ : ∀ᵐ ω ∂(M θ), ∀ j, r j ω + γ * V θ (j + 1) (s (j + 1) ω) - V θ j (s j ω) =
      r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω) :=
    hVc.mono fun ω h j => by rw [h j, h (j + 1)]
  have hbd : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ᵐ ω ∂(M θ), ∀ t,
      ‖∑' k, c ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))‖ ≤
        (1 - c)⁻¹ * M.deltaBound γ := by
    intro c hc'
    filter_upwards [AeAll_LeNorm_TSum_MulPowSubAddRMul_VcVcMulSub1DeltaBound.of.In_Ico.In_Ico (M := M) h₀ h₁ θ hc', hδ] with ω h1 h2 t
    have e : ∑' k, c ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω)) =
        ∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) - M.Vc θ γ (s (t + k) ω)) :=
      tsum_congr fun k => by rw [h2 (t + k)]
    rw [e]
    exact h1 t
  -- the `c`-discounted advantage against the score only sees the first residual
  have hinner : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ t, ∫ ω,
      (∑' k, c ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))) •
        fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) =
      ∫ ω, (r t ω + γ * M.Vc θ γ (s (t + 1) ω) - M.Vc θ γ (s t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    intro c hc' t
    refine (integral_congr_ae ?_).trans
      (Integral_SMul.of.In_Ico.In_Ico (M := M) h₀ h₁ θ hc' t (fun y u => fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ))
    filter_upwards [hscore t, hδ] with ω h1 h2
    rw [h1]
    beta_reduce
    congr 1
    exact tsum_congr fun k => by rw [h2 (t + k)]
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
      (fun (s : ℕ → S) (_ : ℕ → A) (r : ℕ → ℝ) (k : ℕ) => r k + γ * V θ (k + 1) (s (k + 1)) - V θ k (s k))
        (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k := fun k =>
    ((Random.Measurable_R h₁ k).add (((measurable_of_countable (V θ (k + 1))).comp (Random.Measurable_S h₁ (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (V θ k)).comp (Random.Measurable_S h₁ k))
  have hbase : ∇[θ] (
      have : PSpace (M θ) (AsPathRV.path (r)) :=
        PSpace.of_process_path (fun t => ⟨(Random.Measurable_R h₁ t).aemeasurable⟩)
      𝔼[r: M θ](((fun t : ℕ => γ ^ t) @ r))) =
      -- TODO(sympy 𝔼 patch): 𝔽((a₀ t) = … | (s₀ t) = …) with let a₀ := a; let s₀ := s
      let a₀ := a
      let s₀ := s
      𝔼[s, a, r : M θ](
        ∑' t, γ ^ t •
          (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => r (t + k) + γ * V θ (t + k + 1) (s (t + k + 1)) - V θ (t + k) (s (t + k)))) •
            ∇[θ] (ℙ[M θ]((a₀ t) = (a t) | (s₀ t) = (s t)) : ℝ).log)) :=
    Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.All_Differentiable_Prob.GtInftySup.unbiased_advantage_estimate
      h₀ h₁ hS hA h₂ h₃ h₄
  have hA₁ := Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded.Discount
    (X := fun s _ r k => r k + γ * V θ (k + 1) (s (k + 1)) - V θ k (s k)) (c := γ)
    h₀ h₁ hS hA hmeas (hbd γ h₀) h₃ h₄
  have hA₂ := Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded.Discount
    (X := fun s _ r k => r k + γ * V θ (k + 1) (s (k + 1)) - V θ k (s k)) (c := γ * ℓ)
    h₀ h₁ hS hA hmeas (hbd (γ * ℓ) hc) h₃ h₄
  have e : ∑' t, γ ^ t • ∫ ω,
      (∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))) •
        fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω,
      (∑' k, (γ * ℓ) ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))) •
        fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) :=
    tsum_congr fun t => by rw [hinner γ h₀ t, hinner (γ * ℓ) hc t]
  exact hbase.trans (hA₁.symm.trans ((congrArg (InnerProductSpace.toDual ℝ Θ).symm e).trans hA₂))


-- created on 2026-10-01
