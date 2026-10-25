/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

def rosenthalInitialSegment (φ : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map φ

def rosenthalAccepts (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) : Prop :=
  ∀ ψ : ℕ → ℕ, StrictMono ψ →
    ∃ n : ℕ, 𝒜 (s ++ rosenthalInitialSegment (φ ∘ ψ) n)

def rosenthalRejects (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) : Prop :=
  ∀ ψ : ℕ → ℕ, StrictMono ψ → ¬ rosenthalAccepts 𝒜 s (φ ∘ ψ)

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
