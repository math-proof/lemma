/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part6
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_manyChain_succ
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) (n : ℕ) :
    rosenthalManyChain 𝒜 ss φ (n + 1) =
      rosenthalManyNext 𝒜 ss (rosenthalManyChain 𝒜 ss φ n) := by
  rw [show n + 1 = n.succ from rfl]
  exact Function.iterate_succ_apply' (rosenthalManyNext 𝒜 ss) n φ

theorem rosenthal_manyChain_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ n, StrictMono (rosenthalManyChain 𝒜 ss φ n) := by
  intro n
  induction n with
  | zero => exact hφ
  | succ n ih =>
      rw [rosenthal_manyChain_succ]
      exact rosenthal_manyNext_strictMono 𝒜 ss ih

theorem rosenthal_range_manyChain_mono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ)
    {m n : ℕ} (hmn : m ≤ n) :
    Set.range (rosenthalManyChain 𝒜 ss φ n) ⊆
      Set.range (rosenthalManyChain 𝒜 ss φ m) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n hmn ih =>
      rw [rosenthal_manyChain_succ]
      exact (rosenthal_range_manyNext_subset 𝒜 ss _).trans ih

end FunctionalAnalysis.RosenthalL1Wanted
