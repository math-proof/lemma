/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Theorem.Analysis.NormedSpace.RosenthalL1.Part6
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

noncomputable def rosenthalManyPoints
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) (n : ℕ) : ℕ :=
  rosenthalManyChain 𝒜 ss φ n 0

end FunctionalAnalysis.RosenthalL1Wanted
