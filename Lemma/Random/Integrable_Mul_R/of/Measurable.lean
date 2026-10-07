import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.MEqR_Rc
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`ω ↦ φ(X ω) * r[t]` is integrable for a measurable finite-valued `X`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A] [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B]
  {M : Model Θ S A}
-- given
  (X : (ℕ → ℝ × S × A) → B)
  (hX : Measurable X)
  (θ : Θ)
  (φ : B → ℝ)
  (t : ℕ) :
-- imply
  Integrable (fun ω => φ (X ω) * r t ω) (M θ) := by
-- proof
  refine Integrable.of_bound (C := (∑ b, ‖φ b‖) * |M.env.R|) ?_ ((MEqR_Rc (M := M) θ t).mono fun ω h => ?_)
  · exact (((StronglyMeasurable.discrete φ).comp_measurable hX).mul
      (measurable_fst.comp (measurable_pi_apply t)).stronglyMeasurable).aestronglyMeasurable
  ·
    rw [norm_mul, h]
    exact mul_le_mul (Finset.single_le_sum (f := fun b => ‖φ b‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ _)) (NormRc.le.Abs_R (M := M) _) (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))


-- created on 2026-10-07
