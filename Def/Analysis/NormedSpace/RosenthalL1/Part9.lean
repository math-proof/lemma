/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Nth
public import Theorem.Analysis.NormedSpace.RosenthalL1.Part9

@[expose] public section

/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

noncomputable def rosenthalFusionPoints
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) : ℕ :=
  (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).point

end FunctionalAnalysis.RosenthalL1Wanted
