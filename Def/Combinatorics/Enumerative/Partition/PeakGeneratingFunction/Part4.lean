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
public import Abbrev.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part2

@[expose] public section

namespace MetaMathlibExt

def pgf_joinFirst {n m : ℕ} (d : pgfFirstData n m) : Fin n → Fin (m + 1) :=
  fun j =>
    if hlt : j.val < d.1.val then d.2.1 ⟨j.val, hlt⟩ |>.castSucc
    else if heq : j.val = d.1.val then Fin.last m
    else d.2.2 ⟨j.val - d.1.val - 1, by omega⟩

end MetaMathlibExt
