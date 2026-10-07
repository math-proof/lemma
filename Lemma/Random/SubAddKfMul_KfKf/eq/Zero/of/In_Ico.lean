import sympy.stats.policy_trajectory.advantage
import sympy.Basic
import Lemma.Random.EqW
import Lemma.Random.Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.Norm.le.Sum_Norm
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
Bellman identity for the kernel expectations: the one-step expected residual
`Kf rc 1 z + γ * Kf (Vc ∘ state) 2 z - Kf (Vc ∘ state) 1 z` vanishes.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (z : ℝ × S × A) :
-- imply
  M.Kf θ M.rc 1 z + γ * M.Kf θ (fun w => M.Vc θ γ w.2.1) 2 z -
    M.Kf θ (fun w => M.Vc θ γ w.2.1) 1 z = 0 := by
-- proof
  have hf : StronglyMeasurable (fun w : ℝ × S × A => M.Vc θ γ w.2.1) :=
    (StronglyMeasurable.discrete (M.Vc θ γ)).comp_measurable measurable_snd.fst
  have hC : ∀ w : ℝ × S × A, ‖(fun w : ℝ × S × A => M.Vc θ γ w.2.1) w‖ ≤ ∑ y', ‖M.Vc θ γ y'‖ :=
    fun w => Norm.le.Sum_Norm (M.Vc θ γ) w.2.1
  have w0 : ∀ y, M.W θ (fun w : ℝ × S × A => M.Vc θ γ w.2.1) 0 y = M.Vc θ γ y :=
    Random.EqW (M := M) θ (M.Vc θ γ)
  have w1 : ∀ y, M.W θ (fun w : ℝ × S × A => M.Vc θ γ w.2.1) 1 y =
      ∑ u, M.pol.prob θ y u * ∑ y', M.T y u y' * M.Vc θ γ y' := fun y => by
    show M.W θ (fun w : ℝ × S × A => M.Vc θ γ w.2.1) (0 + 1) y = _
    rw [WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 0 y]
    simp_rw [w0]
  have e1 := Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ 0 z
  have e2 := Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 1 z
  have e3 := Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ 0 z
  show M.Kf θ M.rc (0 + 1) z + γ * M.Kf θ (fun w => M.Vc θ γ w.2.1) (1 + 1) z -
      M.Kf θ (fun w => M.Vc θ γ w.2.1) (0 + 1) z = 0
  rw [e1, e2, e3]
  simp_rw [w0, w1]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hrec : M.Vc θ γ y = M.W θ M.rc 0 y +
      γ * ∑ u, M.pol.prob θ y u * ∑ y', M.T y u y' * M.Vc θ γ y' := TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ y
  rw [hrec]
  ring


-- created on 2026-10-06
