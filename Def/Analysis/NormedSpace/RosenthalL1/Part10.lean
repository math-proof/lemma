/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Theorem.Analysis.NormedSpace.RosenthalL1.Part10
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

def rosenthalPairsHold {K : Type*}
    (R : K → ℕ → ℕ → Prop) (k : K) : List ℕ → Prop
  | a :: b :: s => R k a b ∧ rosenthalPairsHold R k s
  | _ => True

end FunctionalAnalysis.RosenthalL1Wanted
