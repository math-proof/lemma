import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory PolicyGradient PolicyGradient.Model

set_option linter.unusedVariables false

/--
Sanity check: `𝔼[s, a, r : M.traj θ](…)` elaborates by flipping each process to its path RV
(`AsPathRV.process`) and taking their finite joint law.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
-- given
  (_hγ : γ ∈ Set.Ico 0 1) :
-- imply
  have hs : ∀ t, PSpace (M.traj θ) (s (S := S) (A := A) t) := fun t =>
    ⟨(s_meas t).aemeasurable⟩
  have ha : ∀ t, PSpace (M.traj θ) (a (S := S) (A := A) t) := fun t =>
    ⟨(a_meas t).aemeasurable⟩
  have hr : ∀ t, PSpace (M.traj θ) (r (S := S) (A := A) t) := fun t =>
    ⟨(r_meas t).aemeasurable⟩
  have : PSpace (M.traj θ) (AsPathRV.path (s (S := S) (A := A))) :=
    PSpace.of_process_path hs
  have : PSpace (M.traj θ) (AsPathRV.path (a (S := S) (A := A))) :=
    PSpace.of_process_path ha
  have : PSpace (M.traj θ) (AsPathRV.path (r (S := S) (A := A))) :=
    PSpace.of_process_path hr
  𝔼[s, a, r : M.traj θ](∑' t, γ ^ t * r t) =
    ∫ ω, ∑' t, γ ^ t * r t ω ∂(M.traj θ) := by
-- proof
  intro _ _ _ _ _ _
  exact Expectation.ofRV_eq_integral
    (f := fun p : (ℕ → S) × (ℕ → A) × (ℕ → ℝ) => ∑' t, γ ^ t * p.2.2 t)
    (by
      refine (Measurable.tsum fun t => ?_).aestronglyMeasurable
      exact ((measurable_pi_apply t).comp measurable_snd |>.comp measurable_snd).const_mul _)


-- created on 2026-09-28
