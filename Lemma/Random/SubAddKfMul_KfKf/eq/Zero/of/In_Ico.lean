import Def.Dynamics.PolicyTrajectory.Gradient
import Lemma.Random.EqW
import Lemma.Random.StronglyMeasurableClip
import Lemma.Random.Vk.eq.Sum_MulProbQk.of.In_Ico.All_Measurable_Prob
import Lemma.Random.W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormClip.le.AbsR
import Lemma.Real.Norm.le.Sum_Norm
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
Bellman identity for the kernel expectations: the one-step expected residual
`Kf (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 z + γ * Kf (V0 ∘ state) 2 z - Kf (V0 ∘ state) 1 z`
vanishes for the series `V0` on every state (no reachability hypothesis).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (z : ℝ × S × A) :
-- imply
  M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 z + γ * M.Kf θ (fun w => M.V0 θ γ w.2.1) 2 z -
    M.Kf θ (fun w => M.V0 θ γ w.2.1) 1 z = 0 := by
-- proof
  classical
  have := M.env.trans_markov
  set f : ℝ × S × A → ℝ := fun w => M.V0 θ γ w.2.1
  have hf : StronglyMeasurable f :=
    (StronglyMeasurable.of_discrete (f := (M.V0 θ γ))).comp_measurable measurable_snd.fst
  have hC : ∀ w : ℝ × S × A, ‖f w‖ ≤ ∑ y', ‖M.V0 θ γ y'‖ :=
    fun w => Norm.le.Sum_Norm (M.V0 θ γ) w.2.1
  have hπ : ∀ θ u, Measurable (fun x : S => M.policy.prob θ x u) :=
    fun _ _ => measurable_of_finite _
  have w0 : ∀ y, ∫ z, f z ∂(M.stageK θ y) = M.V0 θ γ y :=
    fun y => Random.EqW (M := M) θ (M.V0 θ γ) y
  have w0' : ∀ y, ∫ w, M.Kf θ f 0 w ∂(M.stageK θ y) = M.V0 θ γ y := fun y => by
    rw [show M.Kf θ f 0 = f from funext fun w => rfl]
    exact w0 y
  have w1 : ∀ y, ∫ z, M.Kf θ f (0 + 1) z ∂(M.stageK θ y) =
      ∑ u, M.policy.prob θ y u * ∑ y', (M.env.trans (y, u)).real {y'} * M.V0 θ γ y' := fun y => by
    rw [WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 0 y]
    simp_rw [w0']
  have e1 := Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) θ 0 z
  have e2 := Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 1 z
  have e3 := Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 0 z
  show M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) (0 + 1) z + γ * M.Kf θ f (1 + 1) z - M.Kf θ f (0 + 1) z = 0
  rw [e1, e2, e3]
  simp_rw [w0', w1]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hclip0 : ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 z ∂(M.stageK θ y) =
      ∑ u, M.policy.prob θ y u * M.rk y u := by
    have hfC : StronglyMeasurable fun w : ℝ × S × A ↦ clip w.1 (-M.env.R) M.env.R :=
      Random.StronglyMeasurableClip (M := M)
    have hCC : ∀ w : ℝ × S × A, ‖clip w.1 (-M.env.R) M.env.R‖ ≤ |M.env.R| :=
      fun w => NormClip.le.AbsR (M := M) w
    simpa [show M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 =
        (fun z ↦ clip z.1 (-M.env.R) M.env.R) from rfl, Model.rk] using
      W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) hfC hCC θ y
  have hT : ∀ u, ∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u)) =
      ∑ y', (M.env.trans (y, u)).real {y'} * M.V0 θ γ y' := fun u => by
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul, mul_comm]
  have hV : M.V0 θ γ y = ∑ u, M.policy.prob θ y u * M.Qk θ γ y u := by
    change M.Vk θ γ y = _
    exact Vk.eq.Sum_MulProbQk.of.In_Ico.All_Measurable_Prob (M := M) hπ h₀ θ y
  have hrec : M.V0 θ γ y =
      ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 z ∂(M.stageK θ y) +
        γ * ∑ u, M.policy.prob θ y u * ∑ y', (M.env.trans (y, u)).real {y'} * M.V0 θ γ y' := by
    calc
      M.V0 θ γ y
          = ∑ u, M.policy.prob θ y u * M.Qk θ γ y u := hV
      _ = ∑ u, M.policy.prob θ y u *
            (M.rk y u + γ * ∫ y', M.V0 θ γ y' ∂(M.env.trans (y, u))) := by
          rfl
      _ = ∑ u, M.policy.prob θ y u *
            (M.rk y u + γ * ∑ y', (M.env.trans (y, u)).real {y'} * M.V0 θ γ y') := by
          simp_rw [hT]
      _ = ∑ u, M.policy.prob θ y u * M.rk y u +
            γ * ∑ u, M.policy.prob θ y u *
              ∑ y', (M.env.trans (y, u)).real {y'} * M.V0 θ γ y' := by
          simp [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_left_comm]
      _ = ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 z ∂(M.stageK θ y) +
            γ * ∑ u, M.policy.prob θ y u *
              ∑ y', (M.env.trans (y, u)).real {y'} * M.V0 θ γ y' := by
          rw [hclip0]
  rw [hrec]
  ring


-- created on 2026-10-06
-- updated on 2026-11-03
