import Def.Analysis.Calculus.Gradient.Operators.Part2
import Lemma.Random.ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity.All_Eq_JointDens
import Mathlib.Analysis.Calculus.Gradient.Basic
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Real Measure
open scoped ENNReal.ToRealCoe
open IsPolicyTrajectory


/--
Ae equality: binder `∇ log ℙ(a[t]|s[t])` equals `∇ log π_θ` at almost every trajectory.
Under a pointwise joint-density factorization and a positive finite state density,
`OfRealPol` identifies the conditional with the policy density at every parameter, so
the two log-gradients agree.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M] {θ : Θ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}

-- given
  (h₀ : Model.IsPolicyTrajectory M r s a)
  (h₁ : Model.AbsContJointAS M a s)
  (hSm : Model.AbsContStateMarginal M s)
  (h₂ : ∀ θ t aₜ sₜ, (M θ).prob (a t, s t) (aₜ, sₜ) =
    ENNReal.ofReal (M.π[θ] sₜ aₜ) *
      ((M θ).map (s t)).rnDeriv ReferenceMeasure.measure sₜ)
  (h₃ : ∀ θ t x, ((M θ).map (s t)).rnDeriv ReferenceMeasure.measure x ≠ 0)
  (h₄ : ∀ θ t x, ((M θ).map (s t)).rnDeriv ReferenceMeasure.measure x ≠ ⊤) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun θ t =>
    h₀.singlePSpace_as (haj := h₁) θ t
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun θ t =>
    h₀.singlePSpace_s (hac := hSm) θ t
  ∀ t, ∀ᵐ ω ∂(M θ),
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log =
        ∇[θ] (Real.log (M.π[θ] (s t ω) (a t ω))) := by
-- proof
  intro hP _ t
  refine ae_of_all (M θ) fun ω => ?_
  have hfun :
    (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) =
        (fun θ' => Real.log (M.π[θ'] (s t ω) (a t ω))) := by
    funext θ'
    rw [ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity.All_Eq_JointDens
      (M := M) h₀ h₁ (h₂ θ' t (a t ω) (s t ω)) (h₃ θ' t (s t ω)) (h₄ θ' t (s t ω))]
  simp only [gradient]
  exact congrArg (InnerProductSpace.toDual ℝ Θ).symm (congrArg (fun f => fderiv ℝ f θ) hfun)


-- created on 2026-11-13
-- updated on 2026-11-18