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
public import Theorem.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def pgf_rgJoinMap (n k : ℕ) :
    {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} →
      {w : Fin n → Fin (k + 1) // IsSurjectiveRestrictedGrowthString w} :=
  fun d => ⟨pgf_joinFirst d.val,
    (pgf_rg_join_iff d.val.1 d.val.2.1 d.val.2.2).2 d.property⟩

end MetaMathlibExt
