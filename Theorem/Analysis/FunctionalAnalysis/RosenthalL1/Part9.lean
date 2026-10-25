/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.FunctionalAnalysis.RosenthalL1.Part8
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_open_ramsey
    (𝒜 : List ℕ → Prop) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
      ((∀ θ : ℕ → ℕ, StrictMono θ → ∀ n, ¬𝒜 (rosenthalInitialSegment (ψ ∘ θ) n)) ∨
        ∀ θ : ℕ → ℕ, StrictMono θ →
          ∃ n, 𝒜 (rosenthalInitialSegment (ψ ∘ θ) n)) := by
  obtain ⟨η, hη, hdec⟩ := rosenthal_exists_deciding_subsequence 𝒜 [] φ
  let base := φ ∘ η
  have hbase : StrictMono base := hφ.comp hη
  have hrange : Set.range base ⊆ Set.range φ := Set.range_comp_subset_range η φ
  rcases hdec with ha | hr
  · refine ⟨base, hbase, hrange, Or.inr ?_⟩
    intro θ hθ
    obtain ⟨n, hn⟩ := ha θ hθ
    exact ⟨n, by simpa [base] using hn⟩
  · let st := rosenthalFusionInitial 𝒜 base hbase hr
    let ψ := rosenthalFusionPoints 𝒜 st
    have hψ : StrictMono ψ := rosenthal_fusionPoints_strictMono 𝒜 st
    have hψrange : Set.range ψ ⊆ Set.range φ :=
      (rosenthal_range_fusionPoints_subset 𝒜 st).trans hrange
    refine ⟨ψ, hψ, hψrange, Or.inl ?_⟩
    intro θ hθ n
    have hsub := rosenthal_initialSegment_comp_sublist ψ hθ n
    have hchosen : (rosenthalFusionStates 𝒜 st (θ n)).chosen =
        rosenthalInitialSegment ψ (θ n) := by
      exact rosenthal_fusionStates_chosen 𝒜 st rfl (θ n)
    have hmem : rosenthalInitialSegment (ψ ∘ θ) n ∈
        (rosenthalFusionStates 𝒜 st (θ n)).chosen.sublists := by
      rw [hchosen, List.mem_sublists]
      exact hsub
    exact rosenthal_not_mem_of_rejects
      ((rosenthalFusionStates 𝒜 st (θ n)).rejected _ hmem)

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
