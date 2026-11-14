import Lemma.Random.GradVkd.eq.AddIntegral_SMul_Sum_SMul.of.All_EqReal.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico
import Lemma.Random.Pnkd0.eq.Eq
import Lemma.Random.PnkdAdd_1.eq.Sum_MulPnkdP1kd.of.All_EqReal
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
Unrolled policy-gradient recursion for the closed-form value `V0` of a `DensityModel`
with a finite state space: for every initial state `x`,
∇V0(x) = ∑ t < n, γ ^ t • ∑ y, ℙ(s[t] = y | s[0] = x) • ∫ u, (rkd + γ * ∫ V0)(y, u) • ∇π(u | y) du
  + γ ^ n • ∑ y, ℙ(s[n] = y | s[0] = x) • ∇V0(y).
The n-step occupancy is the continuous-action kernel `Pnkd`, and the one-step Bellman
gradient is `GradVkd.eq.AddIntegral_SMul_Sum_SMul`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {p : 𝒮 → 𝒜 → 𝒮 → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₂ : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u)
  (h₃ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₄ : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞)
  (h₅ : ∀ θ x, Measurable (M.policy.prob θ x))
  (h₆ : ∀ x u y, (M.env.trans (x, u)).real {y} = p x u y)
  (n : ℕ)
  (x : 𝒮) :
-- imply
  let S :=
    ∑ t ∈ Finset.range n,
      γ ^ t • ∑ y, M.Pnkd θ t x y •
        (∫ u, ((M.rkd y u + γ * ∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) •
          ∇[θ] M.policy.prob θ y u) ∂ReferenceMeasure.measure)
  ∇[θ] M.V0 θ γ x = S + γ ^ n • ∑ y, M.Pnkd θ n x y • ∇[θ] M.V0 θ γ y := by
-- proof
  have := M.env.trans_markov
  induction n with
  | zero =>
    dsimp only
    simp [Pnkd0.eq.Eq, pow_zero, one_smul]
  | succ n ih =>
    dsimp only at ih ⊢
    have hBell : ∀ y,
        ∇[θ] M.V0 θ γ y =
          (∫ u, ((M.rkd y u + γ * ∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) •
              ∇[θ] M.policy.prob θ y u) ∂ReferenceMeasure.measure) +
            γ • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 θ γ z := by
      intro y
      exact
        GradVkd.eq.AddIntegral_SMul_Sum_SMul.of.All_EqReal.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico
          (M := M) (θ := θ) (t := 0) («\sf{s}» := fun _ => y)
          h₀ h₁ h₂ h₃ h₄ h₅ h₆
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [Finset.sum_congr rfl fun y _ => congrArg (fun v => M.Pnkd θ n x y • v) (hBell y)]
    simp_rw [smul_add, Finset.sum_add_distrib, smul_add]
    congr 1
    calc
      _ = γ ^ n • ∑ y, γ • (M.Pnkd θ n x y • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 θ γ z) := by
        refine congrArg _ (Finset.sum_congr rfl fun y _ => ?_)
        exact smul_comm (M.Pnkd θ n x y) γ _
      _ = γ ^ n • γ • ∑ y, M.Pnkd θ n x y • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 θ γ z := by
        rw [← Finset.smul_sum]
      _ = (γ ^ n * γ) • ∑ y, M.Pnkd θ n x y • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 θ γ z := by
        rw [← mul_smul]
      _ = γ ^ (n + 1) • ∑ y, M.Pnkd θ n x y • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 θ γ z := by
        have hpow : γ ^ n * γ = γ ^ (n + 1) := by
          rw [mul_comm, pow_succ']
        rw [hpow]
      _ = γ ^ (n + 1) • ∑ y, ∑ z, (M.Pnkd θ n x y * M.P1kd θ p y z) • ∇[θ] M.V0 θ γ z := by
        refine congrArg _ (Finset.sum_congr rfl fun y _ => ?_)
        simp [Finset.smul_sum, smul_smul]
      _ = γ ^ (n + 1) • ∑ z, ∑ y, (M.Pnkd θ n x y * M.P1kd θ p y z) • ∇[θ] M.V0 θ γ z := by
        rw [Finset.sum_comm]
      _ = γ ^ (n + 1) • ∑ z, (∑ y, M.Pnkd θ n x y * M.P1kd θ p y z) • ∇[θ] M.V0 θ γ z := by
        refine congrArg _ (Finset.sum_congr rfl fun z _ => ?_)
        rw [← Finset.sum_smul]
      _ = γ ^ (n + 1) • ∑ z, M.Pnkd θ (n + 1) x z • ∇[θ] M.V0 θ γ z := by
        refine congrArg _ (Finset.sum_congr rfl fun z _ => ?_)
        rw [← PnkdAdd_1.eq.Sum_MulPnkdP1kd.of.All_EqReal (M := M) h₆ θ n x z]


-- created on 2026-11-13
