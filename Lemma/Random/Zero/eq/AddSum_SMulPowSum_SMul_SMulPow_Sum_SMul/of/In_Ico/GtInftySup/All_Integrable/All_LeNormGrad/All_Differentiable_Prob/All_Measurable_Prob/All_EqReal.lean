import Lemma.Random.GradVkd.eq.AddIntegral_SMul_Sum_SMul.of.All_EqReal.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico
import Lemma.Random.Pnkd0.eq.Eq
import Lemma.Random.PnkdAdd_1.eq.Sum_MulPnkdP1kd.of.All_EqReal
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Unrolled policy-gradient recursion for the closed-form value `V0` of a `Model`
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
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {γ : ℝ}
  {p : 𝒮 → 𝒜 → 𝒮 → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (h₂ : sup[sₜ] (∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖) ∂ReferenceMeasure.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)) ReferenceMeasure.measure)
  (h₅ : ∀ θ x, Measurable (M.π θ x))
  (h₆ : ∀ x u y, (M.trans (x, u)).toMeasure.real {y} = p x u y)
  (R : ℝ)
  (n : ℕ)
  (sₜ : 𝒮) :
-- imply
  let S :=
    ∑ t ∈ Finset.range n,
      γ ^ t • ∑ y, M.Pnkd θ t sₜ y •
        (∫ u, ((M.rkd R y u + γ * ∫ y', M.V0 R θ γ y' ∂(M.trans (y, u))) •
          ∇[θ] M.π θ y u) ∂ReferenceMeasure.measure)
  ∇[θ] M.V0 R θ γ sₜ = S + γ ^ n • ∑ y, M.Pnkd θ n sₜ y • ∇[θ] M.V0 R θ γ y := by
-- proof
  induction n with
  | zero =>
    dsimp only
    simp [Pnkd0.eq.Eq, pow_zero, one_smul]
  | succ n ih =>
    dsimp only at ih ⊢
    have hBell : ∀ y,
        ∇[θ] M.V0 R θ γ y =
          (∫ u, ((M.rkd R y u + γ * ∫ y', M.V0 R θ γ y' ∂(M.trans (y, u))) •
              ∇[θ] M.π θ y u) ∂ReferenceMeasure.measure) +
            γ • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 R θ γ z := by
      intro y
      exact
        GradVkd.eq.AddIntegral_SMul_Sum_SMul.of.All_EqReal.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico
          (M := M) (θ := θ) (t := 0) («\sf{s}» := fun _ => y) h₀ h₁ h₂ hBdd hIntg h₅ h₆ R
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [Finset.sum_congr rfl fun y _ => congrArg (fun v => M.Pnkd θ n sₜ y • v) (hBell y)]
    simp_rw [smul_add, Finset.sum_add_distrib, smul_add]
    congr 1
    calc
      _ = γ ^ n • ∑ y, γ • (M.Pnkd θ n sₜ y • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 R θ γ z) := by
        refine congrArg _ (Finset.sum_congr rfl fun y _ => ?_)
        exact smul_comm (M.Pnkd θ n sₜ y) γ _
      _ = γ ^ n • γ • ∑ y, M.Pnkd θ n sₜ y • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 R θ γ z := by
        rw [← Finset.smul_sum]
      _ = (γ ^ n * γ) • ∑ y, M.Pnkd θ n sₜ y • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 R θ γ z := by
        rw [← mul_smul]
      _ = γ ^ (n + 1) • ∑ y, M.Pnkd θ n sₜ y • ∑ z, M.P1kd θ p y z • ∇[θ] M.V0 R θ γ z := by
        have hpow : γ ^ n * γ = γ ^ (n + 1) := by
          rw [mul_comm, pow_succ']
        rw [hpow]
      _ = γ ^ (n + 1) • ∑ y, ∑ z, (M.Pnkd θ n sₜ y * M.P1kd θ p y z) • ∇[θ] M.V0 R θ γ z := by
        refine congrArg _ (Finset.sum_congr rfl fun y _ => ?_)
        simp [Finset.smul_sum, smul_smul]
      _ = γ ^ (n + 1) • ∑ z, ∑ y, (M.Pnkd θ n sₜ y * M.P1kd θ p y z) • ∇[θ] M.V0 R θ γ z := by
        rw [Finset.sum_comm]
      _ = γ ^ (n + 1) • ∑ z, (∑ y, M.Pnkd θ n sₜ y * M.P1kd θ p y z) • ∇[θ] M.V0 R θ γ z := by
        refine congrArg _ (Finset.sum_congr rfl fun z _ => ?_)
        rw [← Finset.sum_smul]
      _ = γ ^ (n + 1) • ∑ z, M.Pnkd θ (n + 1) sₜ z • ∇[θ] M.V0 R θ γ z := by
        refine congrArg _ (Finset.sum_congr rfl fun z _ => ?_)
        rw [← PnkdAdd_1.eq.Sum_MulPnkdP1kd.of.All_EqReal (M := M) h₆ θ n sₜ z]


-- created on 2026-11-13
-- updated on 2026-11-18
