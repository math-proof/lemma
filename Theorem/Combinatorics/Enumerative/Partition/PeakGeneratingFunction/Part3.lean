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
import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part6


namespace MetaMathlibExt

@[simp] lemma pgf_last_not_lt_castSucc {m : ℕ} (a : Fin m) :
    ¬Fin.last m < a.castSucc :=
  fun h => (Fin.castSucc_lt_last a).asymm h

@[simp] lemma pgf_last_not_lt {m : ℕ} (a : Fin (m + 1)) :
    ¬Fin.last m < a :=
  not_lt_of_ge (Fin.le_last a)

end MetaMathlibExt
