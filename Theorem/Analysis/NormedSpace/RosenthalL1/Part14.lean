/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part13
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_exists_finite_scalar_net
    {𝕜 : Type*} [RCLike 𝕜] (B δ : ℝ) (hδ : 0 < δ) :
    ∃ t : Finset 𝕜, ∀ z : 𝕜, ‖z‖ ≤ B → ∃ u ∈ t, dist z u ≤ δ := by
  have hcover : Metric.closedBall (0 : 𝕜) B ⊆ ⋃ u, Metric.ball u δ := by
    intro z hz
    rw [Set.mem_iUnion]
    exact ⟨z, Metric.mem_ball_self hδ⟩
  obtain ⟨t, ht⟩ := (ProperSpace.isCompact_closedBall (0 : 𝕜) B).elim_finite_subcover
    (fun u => Metric.ball u δ) (fun _ => Metric.isOpen_ball) hcover
  refine ⟨t, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.closedBall (0 : 𝕜) B := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  have hzt := ht hzball
  simp only [Set.mem_iUnion] at hzt
  obtain ⟨u, hut, hzu⟩ := hzt
  exact ⟨u, hut, (Metric.mem_ball.mp hzu).le⟩

end FunctionalAnalysis.RosenthalL1Wanted
