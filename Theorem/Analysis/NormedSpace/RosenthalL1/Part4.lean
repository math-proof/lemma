/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part4
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_decideMany_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalDecideMany 𝒜 ss φ) := by
  induction ss generalizing φ with
  | nil => exact hφ
  | cons s ss ih =>
      exact ih (hφ.comp (rosenthal_decisionIndices_strictMono 𝒜 s φ))

theorem rosenthal_range_decideMany_subset
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) :
    Set.range (rosenthalDecideMany 𝒜 ss φ) ⊆ Set.range φ := by
  induction ss generalizing φ with
  | nil => exact Set.Subset.rfl
  | cons s ss ih =>
      exact (ih (φ ∘ rosenthalDecisionIndices 𝒜 s φ)).trans
        (Set.range_comp_subset_range _ _)

theorem rosenthal_decideMany_decides
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ s ∈ ss, rosenthalAccepts 𝒜 s (rosenthalDecideMany 𝒜 ss φ) ∨
      rosenthalRejects 𝒜 s (rosenthalDecideMany 𝒜 ss φ) := by
  induction ss generalizing φ with
  | nil => simp
  | cons t ts ih =>
      intro s hs
      let φ' := φ ∘ rosenthalDecisionIndices 𝒜 t φ
      have hφ' : StrictMono φ' :=
        hφ.comp (rosenthal_decisionIndices_strictMono 𝒜 t φ)
      rcases List.mem_cons.mp hs with rfl | hs
      · exact rosenthal_decision_subsequence hφ'
          (rosenthal_decideMany_strictMono 𝒜 ts hφ')
          (rosenthal_range_decideMany_subset 𝒜 ts φ')
          (rosenthal_decisionIndices_decides 𝒜 s φ)
      · exact ih hφ' s hs

end FunctionalAnalysis.RosenthalL1Wanted
