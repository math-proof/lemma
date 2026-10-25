/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Theorem.Analysis.NormedSpace.RosenthalL1.Part7
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

structure RosenthalFusionState (𝒜 : List ℕ → Prop) where
  chosen : List ℕ
  tail : ℕ → ℕ
  tail_strict : StrictMono tail
  rejected : ∀ s ∈ chosen.sublists, rosenthalRejects 𝒜 s tail

structure RosenthalFusionStep
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) where
  point : ℕ
  tail : ℕ → ℕ
  tail_strict : StrictMono tail
  above : ∀ n, point < tail n
  tail_subset : Set.range tail ⊆ Set.range st.tail
  point_mem : point ∈ Set.range st.tail
  rejected : ∀ s ∈ (st.chosen ++ [point]).sublists, rosenthalRejects 𝒜 s tail

end FunctionalAnalysis.RosenthalL1Wanted
