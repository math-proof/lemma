import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`∫ z, 1{s(z) = y} * g z ∂(stageK θ y') = 1{y' = y} * ∫ z, g z ∂(stageK θ y')`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {g : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (hg : StronglyMeasurable g)
  (hC : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ)
  (y y' : S) :
-- imply
  ∫ z, (if z.2.1 = y then (1:ℝ) else 0) * g z ∂(M.stageK θ y') =
    (if y' = y then 1 else 0) * ∫ z, g z ∂(M.stageK θ y') := by
-- proof
  have hm : StronglyMeasurable (fun z : ℝ × S × A => (if z.2.1 = y then (1:ℝ) else 0) * g z) :=
    ((StronglyMeasurable.discrete (fun x : S => if x = y then (1:ℝ) else 0)).comp_measurable measurable_snd.fst).mul hg
  rw [Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable (M := M) hm (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × S × A => z.2.1 = y)) hC) θ, Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable (M := M) hg hC θ]
  by_cases h : y' = y <;> simp [h]


-- created on 2026-10-07
