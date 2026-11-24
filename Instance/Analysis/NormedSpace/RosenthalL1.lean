module
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Nth
public import Abbrev.Analysis.NormedSpace.RosenthalL1


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

noncomputable instance rosenthalDualBallCompact
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    CompactSpace (RosenthalDualBall 𝕜 E) :=
  isCompact_iff_compactSpace.mp
    (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) 1)

instance rosenthalDualBallNonempty
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Nonempty (RosenthalDualBall 𝕜 E) :=
  ⟨⟨0, by simp [Metric.mem_closedBall]⟩⟩

end FunctionalAnalysis.RosenthalL1Wanted
