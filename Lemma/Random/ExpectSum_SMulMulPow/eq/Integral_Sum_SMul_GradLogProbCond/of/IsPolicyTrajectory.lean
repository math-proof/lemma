import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Lemma.Random.PSpace_Path.of.All_PSpace
import sympy.stats.policy_trajectory
import sympy.vector.operators
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real Measure
open IsPolicyTrajectory
open scoped ENNReal.ToRealCoe


/--
Path-binder finset Expect of discounted Q-scaled policy log-gradients equals the
observation Bochner integral of the same sum.
| attributes | lemma |
| :---: | :---: |
| path | Random.ExpectSum_SMulMulPow.eq.Integral_Sum_SMul_GradLogProbCond.of.IsPolicyTrajectory |
| comm | Random.Integral_Sum_SMul_GradLogProbCond.eq.ExpectSum_SMulMulPow.of.IsPolicyTrajectory |
-/
@[path, comm]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ} {γ : ℝ} {n : ℕ}
  {Q : ℕ → S → A → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : IsPolicyTrajectory M r s a) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    IsPolicyTrajectory.singlePSpace_as (h := h₀) _ t
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    IsPolicyTrajectory.singlePSpace_s (h := h₀) _ t
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace fun t => ⟨(h₀.measurable_s t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace fun t => ⟨(h₀.measurable_a t).aemeasurable⟩
  𝔼[s, a : M θ](∑ t ∈ Finset.range n,
      (γ ^ t * Q t (s t) (a t)) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
    ∫ ω, ∑ t ∈ Finset.range n,
      (γ ^ t * Q t (s t ω) (a t ω)) •
        ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log ∂(M θ) := by
-- proof
  intro _ _ _ _
  apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun p : (ℕ → S) × (ℕ → A) ↦
      ∑ t ∈ Finset.range n,
        (γ ^ t * Q t (p.1 t) (p.2 t)) •
          ∇[θ] (ℙ[M θ]((a t) = p.2 t | (s t) = p.1 t) : ℝ).log)
  refine (Finset.stronglyMeasurable_fun_sum (Finset.range n) fun t _ => ?_).aestronglyMeasurable
  apply StronglyMeasurable.comp_measurable
    (f := fun q : S × A ↦
      (γ ^ t * Q t q.1 q.2) • ∇[θ] (ℙ[M θ]((a t) = q.2 | (s t) = q.1) : ℝ).log)
    StronglyMeasurable.of_discrete
    (show Measurable fun p : (ℕ → S) × (ℕ → A) ↦ (p.1 t, p.2 t) from
      ((measurable_pi_apply t).comp measurable_fst).prodMk
        ((measurable_pi_apply t).comp measurable_snd))


-- created on 2026-10-21
