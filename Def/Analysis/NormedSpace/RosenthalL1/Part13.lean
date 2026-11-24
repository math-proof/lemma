module
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Nth
public import Theorem.Analysis.NormedSpace.RosenthalL1.Part13


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

def rosenthalCellPair {K 𝕜 : Type*} [Dist 𝕜]
    (f : ℕ → K → 𝕜) (delta : ℝ) (u v : 𝕜) (k : K) (i j : ℕ) : Prop :=
  dist (f i k) u ≤ delta ∧ dist (f j k) v ≤ delta

end FunctionalAnalysis.RosenthalL1Wanted
