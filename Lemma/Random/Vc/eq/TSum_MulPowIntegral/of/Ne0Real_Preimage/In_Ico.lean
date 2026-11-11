import Def.Dynamics.PolicyTrajectory.Continuous
import Lemma.Random.MeasurableRk
import Def.Dynamics.PolicyTrajectory.Gradient
import Lemma.Random.NormClip.le.AbsR
import Lemma.Random.StronglyMeasurableClip
import Lemma.Random.W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random
set_option linter.unusedVariables false


private lemma Wk_eq_integral_Kf
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  (M : Model Θ S A) (θ : Θ) (k : ℕ) (y : S) :
  M.Wk θ k y =
    ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y) := by
  have hfC : StronglyMeasurable fun w : ℝ × S × A ↦ clip w.1 (-M.env.R) M.env.R :=
    Random.StronglyMeasurableClip (M := M)
  have hCC : ∀ w : ℝ × S × A, ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
    fun w => NormClip.le.AbsR (M := M) w
  induction k generalizing y with
  | zero =>
    have := M.env.reward_markov
    simpa [Model.Wk, Model.rk,
      show M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 =
        (fun z ↦ clip z.1 (-M.env.R) M.env.R) from rfl] using
      (W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) hfC hCC θ y).symm
  | succ k ih =>
    have := M.env.trans_markov
    have hW : ∀ u, ∫ y', M.Wk θ k y' ∂(M.env.trans (y, u)) =
        ∑ y', (M.env.trans (y, u)).real {y'} * M.Wk θ k y' := fun u => by
      rw [integral_fintype Integrable.of_finite]
      simp [smul_eq_mul, mul_comm]
    calc
      M.Wk θ (k + 1) y
          = ∑ u, M.policy.prob θ y u * ∫ y', M.Wk θ k y' ∂(M.env.trans (y, u)) := rfl
      _ = ∑ u, M.policy.prob θ y u *
            ∑ y', (M.env.trans (y, u)).real {y'} * M.Wk θ k y' := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [hW]
      _ = ∑ u, M.policy.prob θ y u *
            ∑ y', (M.env.trans (y, u)).real {y'} *
              ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y') := by
              refine Finset.sum_congr rfl fun u _ => ?_
              refine congrArg _ (Finset.sum_congr rfl fun y' _ => ?_)
              rw [ih]
      _ = ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) (k + 1) z ∂(M.stageK θ y) :=
            (WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
              (M := M) hfC hCC θ k y).symm

/--
The time-free value equals the kernel series on every state (no reachability hypothesis):
`V0 θ γ y = ∑' k, γ ^ k * ∫ z, Kf θ (clip ·.1) k z ∂(stageK θ y)`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (y : S) :
-- imply
  M.V0 θ γ y =
    ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y) := by
-- proof
  unfold Model.V0
  refine tsum_congr fun k => ?_
  rw [Wk_eq_integral_Kf (M := M) θ k y]


-- created on 2026-10-11
-- updated on 2026-11-03
