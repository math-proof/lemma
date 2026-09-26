import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.ForwardSolvesActorBoxEquation.All_In_ActorBox.of.In_ActorBox.ForwardSolvesActorBoxEquation
import Lemma.ForwardSolvesStateEquation.All_StochasticVec.of.StochasticVec.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation


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
-- given
  (h₀ : ForwardSolvesActorBoxEquation data.rTheta θ h)
  (h₁ : ForwardSolvesStateEquation data.delta Q θ μ)
  (h₂ : θ 0 ∈ actor_box d data.rTheta)
  (h₃ : StochasticVec (μ 0))
  (hA : BoxedShortNoteAssumptions data Q) :
-- imply
  ∀ t, 0 ≤ t → (θ t, w t, μ t) ∈ phase_space data := by
-- proof
  intro t ht
  exact ⟨ForwardSolvesActorBoxEquation.All_In_ActorBox.of.In_ActorBox.ForwardSolvesActorBoxEquation h₀ h₂ t ht, ForwardSolvesStateEquation.All_StochasticVec.of.StochasticVec.Gt_0.All_GeneratorMatrix.ForwardSolvesStateEquation h₁ (fun s hs => hA.generator_on_box (θ s) (ForwardSolvesActorBoxEquation.All_In_ActorBox.of.In_ActorBox.ForwardSolvesActorBoxEquation h₀ h₂ s hs)) hA.delta_pos h₃ t ht⟩


-- created on 2026-09-26
