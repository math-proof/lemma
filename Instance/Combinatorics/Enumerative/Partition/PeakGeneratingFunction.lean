/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

@[expose] public section

namespace MetaMathlibExt

/-- Decidability of the restricted-growth predicate (finite quantification). -/
instance (n k : ℕ) : DecidablePred (@IsSurjectiveRestrictedGrowthString n k) := by
  intro w
  unfold IsSurjectiveRestrictedGrowthString Function.Surjective
  infer_instance

end MetaMathlibExt
