/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part8
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

noncomputable def rosenthalFusionStep
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) : RosenthalFusionStep 𝒜 st :=
  Classical.choice (rosenthal_fusionStep_exists 𝒜 st)

noncomputable def rosenthalFusionNext
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) : RosenthalFusionState 𝒜 where
  chosen := st.chosen ++ [(rosenthalFusionStep 𝒜 st).point]
  tail := (rosenthalFusionStep 𝒜 st).tail
  tail_strict := (rosenthalFusionStep 𝒜 st).tail_strict
  rejected := (rosenthalFusionStep 𝒜 st).rejected

def rosenthalFusionInitial
    (𝒜 : List ℕ → Prop) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hrej : rosenthalRejects 𝒜 [] φ) : RosenthalFusionState 𝒜 where
  chosen := []
  tail := φ
  tail_strict := hφ
  rejected := by
    intro s hs
    simp only [List.sublists_nil, List.mem_singleton] at hs
    simpa [hs] using hrej

noncomputable def rosenthalFusionStates
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) :
    RosenthalFusionState 𝒜 :=
  (rosenthalFusionNext 𝒜)^[n] st

noncomputable def rosenthalFusionPoints
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) : ℕ :=
  (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).point

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
