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
import Theorem.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part4


namespace MetaMathlibExt

def pgf_rgJoinMap (n k : ℕ) :
    {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} →
      {w : Fin n → Fin (k + 1) // IsSurjectiveRestrictedGrowthString w} :=
  fun d => ⟨pgf_joinFirst d.val,
    (pgf_rg_join_iff d.val.1 d.val.2.1 d.val.2.2).2 d.property⟩

end MetaMathlibExt
