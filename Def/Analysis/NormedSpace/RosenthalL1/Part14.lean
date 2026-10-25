/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Theorem.Analysis.NormedSpace.RosenthalL1.Part14
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

def rosenthalGap {K alpha : Type*} [Dist alpha]
    (f : ℕ → K → alpha) (epsilon : ℝ) (k : K) (i j : ℕ) : Prop :=
  epsilon ≤ dist (f i k) (f j k)

end FunctionalAnalysis.RosenthalL1Wanted
