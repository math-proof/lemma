/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Nth
public import Def.Analysis.NormedSpace.RosenthalL1.Part3

/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/

public section


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_decisionIndices_strictMono
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) :
    StrictMono (rosenthalDecisionIndices 𝒜 s φ) :=
  (Classical.choose_spec (rosenthal_exists_deciding_subsequence 𝒜 s φ)).1

theorem rosenthal_decisionIndices_decides
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) :
    rosenthalAccepts 𝒜 s (φ ∘ rosenthalDecisionIndices 𝒜 s φ) ∨
      rosenthalRejects 𝒜 s (φ ∘ rosenthalDecisionIndices 𝒜 s φ) :=
  (Classical.choose_spec (rosenthal_exists_deciding_subsequence 𝒜 s φ)).2

end FunctionalAnalysis.RosenthalL1Wanted
