/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring


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
