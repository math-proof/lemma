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
public import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part2
@[expose] public section

namespace MetaMathlibExt

instance {n m : ℕ} (w : Fin n → Fin m) : DecidablePred (pgf_isPeakAt w) := by
  intro i
  unfold pgf_isPeakAt
  infer_instance

end MetaMathlibExt
