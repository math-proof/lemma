/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Theorem.Analysis.NormedSpace.RosenthalL1.Part11
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

def rosenthalPaired {K : Type*}
    (R : K → ℕ → ℕ → Prop) (φ : ℕ → ℕ) : Prop :=
  ∃ k, ∀ n, R k (φ (2 * n)) (φ (2 * n + 1))

def rosenthalPairObstruction {K : Type*}
    (R : K → ℕ → ℕ → Prop) (s : List ℕ) : Prop :=
  ∃ N, s.length = 2 * N ∧ ¬∃ k, rosenthalPairsHold R k s

end FunctionalAnalysis.RosenthalL1Wanted
