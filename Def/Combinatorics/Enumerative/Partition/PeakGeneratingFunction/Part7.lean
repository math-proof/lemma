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
import Theorem.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part3


namespace MetaMathlibExt

def pgf_boundary {n m : ℕ} (d : pgfFirstData n m) : ℕ :=
  if _ : 0 < d.1.val then
    if hv : 0 < n - 1 - d.1.val then
      if d.2.2 ⟨0, hv⟩ < Fin.last m then 1 else 0
    else 0
  else 0

noncomputable def pgf_L (m : ℕ) : pgfR :=
  PowerSeries.mk fun n =>
    if h : 0 < n then
      ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin (m + 1) =>
        w ⟨0, h⟩ < Fin.last m), (Polynomial.X : Polynomial ℤ) ^ pgf_peak w
    else 0

noncomputable def pgf_H (m : ℕ) : pgfR :=
  PowerSeries.mk fun n =>
    ∑ d : pgfFirstData n m, (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d)

noncomputable def pgf_den (m : ℕ) : pgfR :=
  pgf_G (m + 1) - pgf_B * pgf_G m

end MetaMathlibExt
