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
import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part2


namespace MetaMathlibExt

instance {n m : ℕ} (w : Fin n → Fin m) : DecidablePred (pgf_isPeakAt w) := by
  intro i
  unfold pgf_isPeakAt
  infer_instance

end MetaMathlibExt
