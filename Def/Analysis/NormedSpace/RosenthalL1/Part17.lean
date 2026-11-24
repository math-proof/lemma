module
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Nth
public import Theorem.Analysis.NormedSpace.RosenthalL1.Part17


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

noncomputable def rosenthalDualEval
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (n : ℕ) (g : RosenthalDualBall 𝕜 E) : 𝕜 :=
  g.1 (x n)

end FunctionalAnalysis.RosenthalL1Wanted
