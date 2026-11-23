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
public import Theorem.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

@[expose] public section

namespace MetaMathlibExt

def pgf_decodeFirst (n m : ℕ) :
    (Fin n → Fin m) ⊕ pgfFirstData n m → Fin n → Fin (m + 1)
  | Sum.inl u => Fin.castSucc ∘ u
  | Sum.inr d => pgf_joinFirst d

end MetaMathlibExt
