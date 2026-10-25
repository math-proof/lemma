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
import Abbrev.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part2


namespace MetaMathlibExt

def pgf_joinFirst {n m : ℕ} (d : pgfFirstData n m) : Fin n → Fin (m + 1) :=
  fun j =>
    if hlt : j.val < d.1.val then d.2.1 ⟨j.val, hlt⟩ |>.castSucc
    else if heq : j.val = d.1.val then Fin.last m
    else d.2.2 ⟨j.val - d.1.val - 1, by omega⟩

end MetaMathlibExt
