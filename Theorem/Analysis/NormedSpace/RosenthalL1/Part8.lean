/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Structure.Analysis.NormedSpace.RosenthalL1
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_fusionStep_exists
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
    Nonempty (RosenthalFusionStep 𝒜 st) := by
  obtain ⟨m, ψ, hψ, habove, hsub, hmem, hnew⟩ :=
    rosenthal_rejected_extensions_step 𝒜 st.chosen.sublists st.tail_strict st.rejected
  have hold : ∀ s ∈ st.chosen.sublists, rosenthalRejects 𝒜 s ψ := by
    obtain ⟨θ, hθ, hcomp⟩ :=
      rosenthal_exists_indices_of_range_subset st.tail_strict hψ hsub
    intro s hs
    rw [hcomp]
    exact rosenthal_rejects_subsequence (st.rejected s hs) hθ
  refine ⟨⟨m, ψ, hψ, habove, hsub, hmem, ?_⟩⟩
  intro s hs
  rw [List.sublists_concat] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact hold s hs
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hnew t ht

end FunctionalAnalysis.RosenthalL1Wanted
