/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part8
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_fusionStates_succ
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) :
    rosenthalFusionStates 𝒜 st (n + 1) =
      rosenthalFusionNext 𝒜 (rosenthalFusionStates 𝒜 st n) := by
  rw [show n + 1 = n.succ from rfl]
  exact Function.iterate_succ_apply' (rosenthalFusionNext 𝒜) n st

end FunctionalAnalysis.RosenthalL1Wanted
