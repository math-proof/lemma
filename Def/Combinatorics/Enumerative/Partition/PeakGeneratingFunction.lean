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

@[expose] public section

namespace MetaMathlibExt

/-! # Peak generating function for set partitions, Chebyshev form

This file proves the Mansour-Shattuck peak generating function for set partitions,
encoded as surjective restricted-growth strings.
-/

/-- A surjective restricted-growth string: every label smaller than the label
at position `i` already occurs at an earlier position. -/
def IsSurjectiveRestrictedGrowthString {n k : ℕ} (w : Fin n → Fin k) : Prop :=
  Function.Surjective w ∧
    ∀ i : Fin n, ∀ m : Fin k,
      m.val < (w i).val → ∃ j : Fin n, j.val < i.val ∧ w j = m

end MetaMathlibExt
