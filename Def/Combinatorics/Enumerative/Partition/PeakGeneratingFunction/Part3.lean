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
import Instance.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part2


namespace MetaMathlibExt

def pgf_peak {n m : ℕ} (w : Fin n → Fin m) : ℕ :=
  (Finset.univ.filter (pgf_isPeakAt w)).card

def pgf_peakTriples {n m : ℕ} (w : Fin n → Fin m) : ℕ :=
  (Finset.univ.filter fun s : Fin n × Fin n × Fin n =>
    s.1.val + 1 = s.2.1.val ∧ s.2.1.val + 1 = s.2.2.val ∧
      w s.1 < w s.2.1 ∧ w s.2.2 < w s.2.1).card

noncomputable def pgf_W (m : ℕ) : pgfR :=
  PowerSeries.mk fun n => ∑ w : Fin n → Fin m, Polynomial.X ^ pgf_peak w

noncomputable def pgf_PP (k : ℕ) : pgfR :=
  PowerSeries.mk fun n => ∑ w ∈ Finset.univ.filter
    (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    Polynomial.X ^ pgf_peak w

def pgf_peakNat {m K : ℕ} (w : Fin m → Fin K) (v : ℕ) : ℕ :=
  if h : v < m then
    if _ : 0 < v then
      if hv1 : v + 1 < m then
        if w ⟨v - 1, lt_of_le_of_lt (Nat.sub_le v 1) h⟩ < w ⟨v, h⟩ ∧
            w ⟨v + 1, hv1⟩ < w ⟨v, h⟩ then 1 else 0
      else 0
    else 0
  else 0

end MetaMathlibExt
