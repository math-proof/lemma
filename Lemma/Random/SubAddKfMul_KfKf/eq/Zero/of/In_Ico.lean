import Lemma.Random.EqW
import Lemma.Random.TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
Bellman identity for the kernel expectations: the one-step expected residual
`Kf (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 z + γ * Kf (Vc ∘ state) 2 z - Kf (Vc ∘ state) 1 z` vanishes
when every state is reachable at time 0.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (z : ℝ × S × A)
  (hP : ∀ y, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) ≠ 0) :
-- imply
  M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 1 z + γ * M.Kf θ (fun w => M.Vc θ γ w.2.1) 2 z -
    M.Kf θ (fun w => M.Vc θ γ w.2.1) 1 z = 0 := by
-- proof
  set f : ℝ × S × A → ℝ := fun w => M.Vc θ γ w.2.1
  have hf : StronglyMeasurable f :=
    (StronglyMeasurable.of_discrete (f := (M.Vc θ γ))).comp_measurable measurable_snd.fst
  have hC : ∀ w : ℝ × S × A, ‖f w‖ ≤ ∑ y', ‖M.Vc θ γ y'‖ :=
    fun w => Norm.le.Sum_Norm (M.Vc θ γ) w.2.1
  have w0 : ∀ y, ∫ z, f z ∂(M.stageK θ y) = M.Vc θ γ y :=
    fun y => Random.EqW (M := M) θ (M.Vc θ γ) y
  have w0' : ∀ y, ∫ w, M.Kf θ f 0 w ∂(M.stageK θ y) = M.Vc θ γ y := fun y => by
    rw [show M.Kf θ f 0 = f from funext fun w => rfl]
    exact w0 y
  have w1 : ∀ y, ∫ z, M.Kf θ f (0 + 1) z ∂(M.stageK θ y) =
      ∑ u, M.policy.prob θ y u * ∑ y', (M.env.trans (y, u)).real {y'} * M.Vc θ γ y' := fun y => by
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
  have hrec : M.Vc θ γ y = ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) 0 z ∂(M.stageK θ y) +
      γ * ∑ u, M.policy.prob θ y u * ∑ y', (M.env.trans (y, u)).real {y'} * M.Vc θ γ y' := by
    rw [Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) h₀ θ y (hP y),
      TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ y]
    congr 2
    refine Finset.sum_congr rfl fun u _ => congrArg (M.policy.prob θ y u * ·) ?_
    refine Finset.sum_congr rfl fun yInner _ => congrArg ((M.env.trans (y, u)).real {yInner} * ·) ?_
    simpa using (Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) h₀ θ yInner (hP yInner)).symm
  rw [hrec]
  ring


-- created on 2026-10-06
-- updated on 2026-10-20
