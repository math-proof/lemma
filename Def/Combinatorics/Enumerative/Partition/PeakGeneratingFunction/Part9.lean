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
import Theorem.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part5


namespace MetaMathlibExt

noncomputable def pgf_rgJoinEquiv (n k : ℕ) :
    {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1} ≃
      {w : Fin n → Fin (k + 1) // IsSurjectiveRestrictedGrowthString w} :=
  Equiv.ofBijective (pgf_rgJoinMap n k)
    ⟨pgf_rgJoinMap_injective n k, pgf_rgJoinMap_surjective n k⟩

noncomputable def pgf_PH (k : ℕ) : pgfR :=
  PowerSeries.mk fun n =>
    ∑ d ∈ Finset.univ.filter
      (fun d : pgfFirstData n k => IsSurjectiveRestrictedGrowthString d.2.1),
      (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d)

noncomputable def pgf_F (j : ℕ) : pgfR :=
  1 + pgf_x * (1 - pgf_q) * pgf_W j + pgf_q * (pgf_W j - 1)

noncomputable def pgf_r (j : ℕ) : pgfK :=
  pgf_map (pgf_G (j + 1)) / pgf_map (pgf_G j)

end MetaMathlibExt
