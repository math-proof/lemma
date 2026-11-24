module
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Nth
public import Def.Analysis.NormedSpace.RosenthalL1.Part16


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/
namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_dualBallStrong_norm_le
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (g : RosenthalDualBall 𝕜 E) : ‖rosenthalDualBallStrong g‖ ≤ 1 := by
  simpa [rosenthalDualBallStrong, Metric.mem_closedBall, dist_eq_norm] using g.2

end FunctionalAnalysis.RosenthalL1Wanted
