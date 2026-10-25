/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.FunctionalAnalysis.RosenthalL1.Part5
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_manyNext_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalManyNext 𝒜 ss φ) :=
  rosenthal_decideMany_strictMono 𝒜 _ (rosenthal_tail_strictMono hφ)

theorem rosenthal_range_manyNext_subset
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) :
    Set.range (rosenthalManyNext 𝒜 ss φ) ⊆ Set.range φ := by
  exact (rosenthal_range_decideMany_subset 𝒜 _ _).trans
    (Set.range_comp_subset_range (fun n => n + 1) φ)

theorem rosenthal_manyNext_above
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ n, φ 0 < rosenthalManyNext 𝒜 ss φ n := by
  intro n
  obtain ⟨k, hk⟩ := rosenthal_range_decideMany_subset 𝒜
    (ss.map fun s => s ++ [φ 0]) (rosenthalTail φ) ⟨n, rfl⟩
  change φ 0 < rosenthalDecideMany 𝒜
    (ss.map fun s => s ++ [φ 0]) (rosenthalTail φ) n
  rw [← hk]
  exact hφ (Nat.zero_lt_succ k)

theorem rosenthal_manyNext_decides
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ s ∈ ss, rosenthalAccepts 𝒜 (s ++ [φ 0]) (rosenthalManyNext 𝒜 ss φ) ∨
      rosenthalRejects 𝒜 (s ++ [φ 0]) (rosenthalManyNext 𝒜 ss φ) := by
  intro s hs
  exact rosenthal_decideMany_decides 𝒜 _ (rosenthal_tail_strictMono hφ)
    (s ++ [φ 0]) (List.mem_map.mpr ⟨s, hs, rfl⟩)

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
