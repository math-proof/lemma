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
import Theorem.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part2


namespace MetaMathlibExt

noncomputable def pgf_firstTopEquiv (n m : ℕ) :
    ((Fin n → Fin m) ⊕ pgfFirstData n m) ≃ (Fin n → Fin (m + 1)) :=
  Equiv.ofBijective (pgf_decodeFirst n m)
    ⟨pgf_decodeFirst_injective n m, pgf_decodeFirst_surjective n m⟩

end MetaMathlibExt
