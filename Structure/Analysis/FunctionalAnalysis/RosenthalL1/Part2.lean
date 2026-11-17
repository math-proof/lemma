/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Nth
public import Def.Analysis.FunctionalAnalysis.RosenthalL1.Part13
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/
public section




namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

structure RosenthalSequenceState where
  seq : ℕ → ℕ
  strict : StrictMono seq

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
