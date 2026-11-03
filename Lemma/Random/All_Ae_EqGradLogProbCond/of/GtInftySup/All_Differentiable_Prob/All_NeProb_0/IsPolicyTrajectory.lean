import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Mathlib.Analysis.Calculus.Gradient.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Real Measure
open scoped ENNReal.ToRealCoe
open IsPolicyTrajectory
set_option linter.unusedVariables false


/--
Ae equality: binder `∇ log ℙ(a[t]|s[t])` equals `∇ log π_θ` at almost every trajectory
(visited states are reachable a.s., so `OfRealPol` applies pathwise). Diff/Sup are on the
policy mass function (no global joint / state-support hypothesis).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : IsPolicyTrajectory M r s a)
  (hDiff : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (hSup : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    IsPolicyTrajectory.singlePSpace_as (h := h₀) _ t
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    IsPolicyTrajectory.singlePSpace_s (h := h₀) _ t
  ∀ t, ∀ᵐ ω ∂(M θ),
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log =
        ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) := by
-- proof
  intro hP _
  have : IsPolicyTrajectory M r s a := h₀
  classical
  intro t
  filter_upwards [AeRealPreimageSS.ne.Zero (s := ⇑s) (M := M) θ] with ω hω
  have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
    (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M)
      h₀.stage_eq hDiff hSup t (s t ω) θ).continuousAt
  have hfd :
    fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₀.stage_eq (hP θ' t) h,
      ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  simp only [gradient]
  apply congrArg (InnerProductSpace.toDual ℝ Θ).symm hfd


-- created on 2026-10-21
-- updated on 2026-11-03
