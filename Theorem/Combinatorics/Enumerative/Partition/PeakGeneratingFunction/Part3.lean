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
public import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

@[simp] lemma pgf_last_not_lt_castSucc {m : ℕ} (a : Fin m) :
    ¬Fin.last m < a.castSucc :=
  fun h => (Fin.castSucc_lt_last a).asymm h

@[simp] lemma pgf_last_not_lt {m : ℕ} (a : Fin (m + 1)) :
    ¬Fin.last m < a :=
  not_lt_of_ge (Fin.le_last a)

end MetaMathlibExt
