/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part11
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

def rosenthalPairLift (η : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * η (n / 2) + n % 2

def rosenthalCellPair {K 𝕜 : Type*} [Dist 𝕜]
    (f : ℕ → K → 𝕜) (delta : ℝ) (u v : 𝕜) (k : K) (i j : ℕ) : Prop :=
  dist (f i k) u ≤ delta ∧ dist (f j k) v ≤ delta

def rosenthalGap {K alpha : Type*} [Dist alpha]
    (f : ℕ → K → alpha) (epsilon : ℝ) (k : K) (i j : ℕ) : Prop :=
  epsilon ≤ dist (f i k) (f j k)

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
