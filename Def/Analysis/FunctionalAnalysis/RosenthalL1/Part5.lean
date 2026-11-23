/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Nth
public import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part4

@[expose] public section

/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

noncomputable def rosenthalManyNext
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) : ℕ → ℕ :=
  rosenthalDecideMany 𝒜 (ss.map fun s => s ++ [φ 0]) (rosenthalTail φ)

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
