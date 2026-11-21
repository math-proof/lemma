import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Lemma.Random.PSpace_Path.of.All_PSpace
import Instance.Probability.Moments.Variance
import Class.Dynamics.PolicyTrajectory
import Def.Analysis.Calculus.Gradient.Operators
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real Measure
open scoped ENNReal.ToRealCoe


/--
Path-binder finset Expect of discounted Q-scaled policy log-gradients equals the
Bochner integral of the same sum.
| attributes | lemma |
| :---: | :---: |
| path | Random.ExpectSum_SMulMulPow.eq.Integral_Sum_SMul_GradLogProbCond.of.IsPolicyTrajectory |
| comm | Random.Integral_Sum_SMul_GradLogProbCond.eq.ExpectSum_SMulMulPow.of.IsPolicyTrajectory |
-/
@[path, comm]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M] {θ : Θ} {γ : ℝ} {n : ℕ}
  {Q : ℕ → 𝒮 → 𝒜 → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : Model.IsPolicyTrajectory M r s a)
  (h₁ : Model.AbsContJointAS M a s)
  (h₂ : Model.AbsContStateMarginal M s) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun θ t =>
    h₀.singlePSpace_as (haj := h₁) θ t
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun θ t =>
    h₀.singlePSpace_s (hac := h₂) θ t
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace fun t => ⟨(h₀.measurable_s t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace fun t => ⟨(h₀.measurable_a t).aemeasurable⟩
  𝔼[s, a : M θ](∑ t ∈ Finset.range n,
      (γ ^ t * Q t (s t) (a t)) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
    ∫ ω, (∑ t ∈ Finset.range n,
      (γ ^ t * Q t (s t ω) (a t ω)) •
        ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) ∂(M θ) := by
-- proof
  intro _ _ _ _
  apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun p : (ℕ → 𝒮) × (ℕ → 𝒜) ↦
      ∑ t ∈ Finset.range n,
        (γ ^ t * Q t (p.1 t) (p.2 t)) •
          ∇[θ] (ℙ[M θ]((a t) = p.2 t | (s t) = p.1 t) : ℝ).log)
  refine (Finset.stronglyMeasurable_fun_sum (Finset.range n) fun t _ => ?_).aestronglyMeasurable
  apply StronglyMeasurable.comp_measurable
    (f := fun q : 𝒮 × 𝒜 ↦
      (γ ^ t * Q t q.1 q.2) • ∇[θ] (ℙ[M θ]((a t) = q.2 | (s t) = q.1) : ℝ).log)
    StronglyMeasurable.of_discrete
    (show Measurable fun p : (ℕ → 𝒮) × (ℕ → 𝒜) ↦ (p.1 t, p.2 t) from
      ((measurable_pi_apply t).comp measurable_fst).prodMk
        ((measurable_pi_apply t).comp measurable_snd))


-- created on 2026-10-21
-- updated on 2026-11-18