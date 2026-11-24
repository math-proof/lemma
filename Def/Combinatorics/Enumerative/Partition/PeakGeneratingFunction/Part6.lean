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
public import Theorem.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

noncomputable def pgf_firstTopEquiv (n m : ℕ) :
    ((Fin n → Fin m) ⊕ pgfFirstData n m) ≃ (Fin n → Fin (m + 1)) :=
  Equiv.ofBijective (pgf_decodeFirst n m)
    ⟨pgf_decodeFirst_injective n m, pgf_decodeFirst_surjective n m⟩

end MetaMathlibExt
