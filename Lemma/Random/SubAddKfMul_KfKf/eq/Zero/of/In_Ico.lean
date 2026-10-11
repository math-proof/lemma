import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.EqW
import Lemma.Random.Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormRc.le.AbsR
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.In_Ico
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm.le.Sum_Norm
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
Bellman identity for the kernel expectations: the one-step expected residual
`Kf rc 1 z + γ * Kf (Vc ∘ state) 2 z - Kf (Vc ∘ state) 1 z` vanishes.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (z : ℝ × S × A) :
-- imply
  let rc (z : ℝ × S × A) : ℝ := clip z.1 (-M.env.R) M.env.R
  M.Kf θ rc 1 z + γ * M.Kf θ (fun w => M.Vc θ γ w.2.1) 2 z -
    M.Kf θ (fun w => M.Vc θ γ w.2.1) 1 z = 0 := by
-- proof
  intro rc
  set f : ℝ × S × A → ℝ := fun w => M.Vc θ γ w.2.1
  have hf : StronglyMeasurable f :=
    (StronglyMeasurable.discrete (M.Vc θ γ)).comp_measurable measurable_snd.fst
  have hC : ∀ w : ℝ × S × A, ‖f w‖ ≤ ∑ y', ‖M.Vc θ γ y'‖ :=
    fun w => Norm.le.Sum_Norm (M.Vc θ γ) w.2.1
  have w0 : ∀ y, ∫ z, f z ∂(M.stageK θ y) = M.Vc θ γ y :=
    fun y => Random.EqW (M := M) θ (M.Vc θ γ) y
  have w0' : ∀ y, ∫ w, M.Kf θ f 0 w ∂(M.stageK θ y) = M.Vc θ γ y := fun y => by
    rw [show M.Kf θ f 0 = f from funext fun w => rfl]
    exact w0 y
  have w1 : ∀ y, ∫ z, M.Kf θ f (0 + 1) z ∂(M.stageK θ y) =
      ∑ u, M.pol.prob θ y u * ∑ y', (M.env.trans (y, u)).real {y'} * M.Vc θ γ y' := fun y => by
    rw [WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 0 y]
    simp_rw [w0']
  have e1 := Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.AbsR (M := M)) θ 0 z
  have e2 := Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 1 z
  have e3 := Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 0 z
  show M.Kf θ rc (0 + 1) z + γ * M.Kf θ f (1 + 1) z - M.Kf θ f (0 + 1) z = 0
  rw [e1, e2, e3]
  simp_rw [w0', w1]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hrec : M.Vc θ γ y = ∫ z, M.Kf θ rc 0 z ∂(M.stageK θ y) +
      γ * ∑ u, M.pol.prob θ y u * ∑ y', (M.env.trans (y, u)).real {y'} * M.Vc θ γ y' := by
    rw [Vc.eq.TSum_MulPowIntegral.of.In_Ico (M := M) (γ := γ) θ y,
      TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ y]
    congr 2
    refine Finset.sum_congr rfl fun u _ => congrArg (M.pol.prob θ y u * ·) ?_
    refine Finset.sum_congr rfl fun yInner _ => congrArg ((M.env.trans (y, u)).real {yInner} * ·) ?_
    simpa [rc] using (Vc.eq.TSum_MulPowIntegral.of.In_Ico (M := M) (γ := γ) θ yInner).symm
  rw [hrec]
  simp_rw [show (fun z => clip z.1 (-M.env.R) M.env.R) = rc from funext fun z => by simp [rc]]
  ring


-- created on 2026-10-06
-- updated on 2026-10-11
