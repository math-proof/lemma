import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.ForwardSolvesCriticEquation.All_LeNorm.of.LeNorm.IsValidCriticRadius.ForwardUniformCriticDriftBound.ForwardUniformCriticCoercive.ForwardSolvesCriticEquation
import Lemma.BoxedShortNoteAssumptions.All_In_PhaseSpace.of.StochasticVec.In_ActorBox.ForwardSolvesStateEquation.ForwardSolvesActorBoxEquation


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {A : Type*} [Fintype A]
  {d : ℕ}
  {m : ℕ}
  {data : BoxedFiniteStateData S A d m}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : ℝ → EuclideanVec d}
  {h : ℝ → EuclideanVec d}
  {w : ℝ → EuclideanVec m}
  {μ : ℝ → S → ℝ}
  {Bb : ℝ}
  {rW : ℝ}
  {Am : ℝ → Matrix (Fin m) (Fin m) ℝ}
  {b : ℝ → EuclideanVec m}
-- given
  (h₀ : ForwardSolvesActorBoxEquation data.rTheta θ h)
  (h₁ : ForwardSolvesStateEquation data.delta Q θ μ)
  (h₂ : θ 0 ∈ actor_box d data.rTheta)
  (h₃ : StochasticVec (μ 0))
  (h₄ : ForwardSolvesCriticEquation Am b w)
  (h₅ : ForwardUniformCriticCoercive data.lambdaC Am)
  (h₆ : ForwardUniformCriticDriftBound Bb b)
  (h₇ : IsValidCriticRadius data.lambdaC Bb rW)
  (h₈ : ‖w 0‖ ≤ rW)
  (hA : BoxedShortNoteAssumptions data Q) :
-- imply
  ∀ t, 0 ≤ t → (θ t, w t, μ t) ∈ absorbing_set data rW := by
-- proof
  intro t ht
  have h₉ : (θ t, w t, μ t) ∈ phase_space data := BoxedShortNoteAssumptions.All_In_PhaseSpace.of.StochasticVec.In_ActorBox.ForwardSolvesStateEquation.ForwardSolvesActorBoxEquation h₀ h₁ h₂ h₃ hA t ht
  exact ⟨h₉.1, mem_closedBall_zero_iff.2 (ForwardSolvesCriticEquation.All_LeNorm.of.LeNorm.IsValidCriticRadius.ForwardUniformCriticDriftBound.ForwardUniformCriticCoercive.ForwardSolvesCriticEquation h₄ h₅ h₆ h₇ h₈ t ht), h₉.2⟩


-- created on 2026-09-26
