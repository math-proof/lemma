/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part4


namespace StatMech

namespace Exact3D

namespace FKReparameterization

theorem expLogUpperComparisonPrefactor_pos
    (lo hi k : ℝ) :
    0 < expLogUpperComparisonPrefactor lo hi k := by
  by_cases hk : 0 ≤ k
  · simpa [expLogUpperComparisonPrefactor, hk] using
      Real.exp_pos (k * Real.log hi)
  · simpa [expLogUpperComparisonPrefactor, hk] using
      Real.exp_pos (k * Real.log lo)

set_option linter.style.longLine false in


theorem exp_log_upper_power_transfer_of_comparable
    {lo hi d p k : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) (hd : 0 < d)
    (hlo_comp : lo * d ≤ p) (hhi_comp : p ≤ hi * d) :
    Real.exp (k * Real.log p) ≤
      expLogUpperComparisonPrefactor lo hi k *
        Real.exp (k * Real.log d) := by
  by_cases hk : 0 ≤ k
  · have hp : 0 < p := lt_of_lt_of_le (mul_pos hlo hd) hlo_comp
    have hbase :
        Real.exp (k * Real.log p) ≤
          Real.exp (k * Real.log hi) *
            Real.exp (k * Real.log d) := by
      rw [← Real.exp_add]
      rw [Real.exp_le_exp]
      have hlogcomp : Real.log p ≤ Real.log (hi * d) :=
        Real.log_le_log hp hhi_comp
      have hlogmul : Real.log (hi * d) = Real.log hi + Real.log d := by
        rw [Real.log_mul hhi.ne' hd.ne']
      have hlogcomp' : Real.log p ≤ Real.log hi + Real.log d := by
        simpa [hlogmul] using hlogcomp
      calc
        k * Real.log p ≤ k * (Real.log hi + Real.log d) :=
          mul_le_mul_of_nonneg_left hlogcomp' hk
        _ = k * Real.log hi + k * Real.log d := by ring
    simpa [expLogUpperComparisonPrefactor, hk] using hbase
  · have hk_le : k ≤ 0 := le_of_not_ge hk
    have hbase :
        Real.exp (k * Real.log p) ≤
          Real.exp (k * Real.log lo) *
            Real.exp (k * Real.log d) := by
      rw [← Real.exp_add]
      rw [Real.exp_le_exp]
      have hlogcomp : Real.log (lo * d) ≤ Real.log p :=
        Real.log_le_log (mul_pos hlo hd) hlo_comp
      have hlogmul : Real.log (lo * d) = Real.log lo + Real.log d := by
        rw [Real.log_mul hlo.ne' hd.ne']
      have hlogcomp' : Real.log lo + Real.log d ≤ Real.log p := by
        simpa [hlogmul] using hlogcomp
      calc
        k * Real.log p ≤ k * (Real.log lo + Real.log d) :=
          mul_le_mul_of_nonpos_left hlogcomp' hk_le
        _ = k * Real.log lo + k * Real.log d := by ring
    simpa [expLogUpperComparisonPrefactor, hk] using hbase


theorem pOfBeta_leftCriticalReparam (βc : ℝ) :
    LeftCriticalReparam (ParameterModel βc)
      (ParameterModel (IsingFK.pOfBeta βc)) IsingFK.pOfBeta where
  tendsto_left := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : ContinuousAt IsingFK.pOfBeta βc := by
        unfold IsingFK.pOfBeta
        fun_prop
      simpa [ParameterModel] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      simpa [ParameterModel] using pOfBeta_strictMono hβ
  log_distance_ratio := by
    let L := nhdsWithin βc (Set.Iio βc)
    have hlogpref :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (pOfBetaDistancePrefactor βc β) / Real.log (βc - β))
          L (nhds 0) := by
      simpa [L] using tendsto_log_pOfBetaDistancePrefactor_div_log_left βc
    have hlim :
        Filter.Tendsto
          (fun β : ℝ =>
            1 + Real.log (pOfBetaDistancePrefactor βc β) /
              Real.log (βc - β))
          L (nhds (1 + 0)) :=
      tendsto_const_nhds.add hlogpref
    refine Filter.Tendsto.congr' ?_ (by simpa using hlim)
    filter_upwards
      [self_mem_nhdsWithin,
        Ioo_mem_nhdsLT (show βc - 1 < βc by linarith)] with β hβ hβnear
    have hdiff_pos : 0 < βc - β := sub_pos.mpr hβ
    have hdiff_ne : βc - β ≠ 0 := hdiff_pos.ne'
    have hpref_pos : 0 < pOfBetaDistancePrefactor βc β := by
      unfold pOfBetaDistancePrefactor
      exact div_pos (sub_pos.mpr (pOfBeta_strictMono hβ)) hdiff_pos
    have hpref_ne : pOfBetaDistancePrefactor βc β ≠ 0 := hpref_pos.ne'
    have hdiff_lt_one : βc - β < 1 := by
      linarith [hβnear.1]
    have hlogd_ne : Real.log (βc - β) ≠ 0 :=
      (Real.log_neg hdiff_pos hdiff_lt_one).ne
    have hdist :
        IsingFK.pOfBeta βc - IsingFK.pOfBeta β =
          pOfBetaDistancePrefactor βc β * (βc - β) := by
      unfold pOfBetaDistancePrefactor
      field_simp [hdiff_ne]
    rw [show (ParameterModel (IsingFK.pOfBeta βc)).betaC - IsingFK.pOfBeta β =
        IsingFK.pOfBeta βc - IsingFK.pOfBeta β by rfl]
    rw [show (ParameterModel βc).betaC - β = βc - β by rfl]
    rw [hdist, Real.log_mul hpref_ne hdiff_ne]
    field_simp [hlogd_ne]
    ring

set_option linter.style.longLine false in


theorem eventually_pOfBeta_mem_Ioo_left {βc pδ : ℝ} (hpδ : 0 < pδ) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
      IsingFK.pOfBeta β ∈
        Set.Ioo (IsingFK.pOfBeta βc - pδ) (IsingFK.pOfBeta βc) := by
  have hpIoo :
      Set.Ioo (IsingFK.pOfBeta βc - pδ) (IsingFK.pOfBeta βc) ∈
        nhdsWithin (IsingFK.pOfBeta βc) (Set.Iio (IsingFK.pOfBeta βc)) :=
    Ioo_mem_nhdsLT (show IsingFK.pOfBeta βc - pδ < IsingFK.pOfBeta βc by
      linarith)
  exact (pOfBeta_leftCriticalReparam βc).tendsto_left.eventually hpIoo

set_option linter.style.longLine false in

theorem exists_pOfBeta_mem_Ioo_left {βc pδ : ℝ} (hpδ : 0 < pδ) :
    ∃ δ, 0 < δ ∧
      ∀ β, β ∈ Set.Ioo (βc - δ) βc →
        IsingFK.pOfBeta β ∈
          Set.Ioo (IsingFK.pOfBeta βc - pδ) (IsingFK.pOfBeta βc) :=
  exists_Ioo_subset_of_eventually_left
    (eventually_pOfBeta_mem_Ioo_left (βc := βc) hpδ)

end FKReparameterization
end Exact3D
end StatMech
