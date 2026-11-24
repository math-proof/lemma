module
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Nth
public import Theorem.Analysis.NormedSpace.RosenthalL1.Part15


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/
namespace FunctionalAnalysis.RosenthalL1Wanted

def rosenthalAssignmentIndices (P : Finset ℕ) (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    if n / 2 ∈ P then 3 * (n / 2) + 1 else 3 * (n / 2)
  else
    if n / 2 ∈ P then 3 * (n / 2) + 2 else 3 * (n / 2) + 1

end FunctionalAnalysis.RosenthalL1Wanted
