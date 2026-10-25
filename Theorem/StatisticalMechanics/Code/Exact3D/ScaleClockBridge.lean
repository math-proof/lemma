/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem tendsto_scaleClock_ratio_of_eventually_annulus {ι : Type*}
    (M : CriticalModel ι) (clock : ℝ → ℝ)
    (relevantEigenvalue cLo cHi : ℝ)
    (heigen : 1 < relevantEigenvalue) (hcLo : 0 < cLo)
    (_hcHi : 0 < cHi)
    (hannulus :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ∧
          Real.exp (clock β * Real.log relevantEigenvalue) *
              (M.betaC - β) ≤ cHi) :
    Filter.Tendsto
      (fun β : ℝ => clock β / (-Real.log (M.betaC - β)))
      (nhdsWithin M.betaC (Set.Iio M.betaC))
      (nhds ((Real.log relevantEigenvalue)⁻¹)) := by
  let L := nhdsWithin M.betaC (Set.Iio M.betaC)
  let logEigen := Real.log relevantEigenvalue
  have hlogEigen_pos : 0 < logEigen := by
    simpa [logEigen] using Real.log_pos heigen
  have hneglog :
      Filter.Tendsto (fun β : ℝ => -Real.log (M.betaC - β))
        L Filter.atTop := by
    change
      Filter.Tendsto (fun β : ℝ => -(Real.log (M.betaC - β)))
        L Filter.atTop
    exact
      ((Filter.tendsto_neg_atBot_atTop :
        Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop).comp
          (by simpa [L] using tendsto_log_betaC_sub_atBot M))
  have hlo_term :
      Filter.Tendsto
        (fun β : ℝ => Real.log cLo / (-Real.log (M.betaC - β)))
        L (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hneglog
  have hhi_term :
      Filter.Tendsto
        (fun β : ℝ => Real.log cHi / (-Real.log (M.betaC - β)))
        L (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hneglog
  have hlo_limit :
      Filter.Tendsto
        (fun β : ℝ =>
          (1 + Real.log cLo / (-Real.log (M.betaC - β))) / logEigen)
        L (nhds (logEigen⁻¹)) := by
    have hsum :=
      ((tendsto_const_nhds (x := (1 : ℝ))).add hlo_term).const_mul
        logEigen⁻¹
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hhi_limit :
      Filter.Tendsto
        (fun β : ℝ =>
          (1 + Real.log cHi / (-Real.log (M.betaC - β))) / logEigen)
        L (nhds (logEigen⁻¹)) := by
    have hsum :=
      ((tendsto_const_nhds (x := (1 : ℝ))).add hhi_term).const_mul
        logEigen⁻¹
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_limit hhi_limit ?_ ?_
  · filter_upwards
      [hannulus,
        Ioo_mem_nhdsLT (show M.betaC - (1 : ℝ) < M.betaC by norm_num)]
      with β hb hβdist
    let x := -Real.log (M.betaC - β)
    have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβdist.1, hβdist.2]
    have hxpos : 0 < x := by
      have hlogneg : Real.log (M.betaC - β) < 0 :=
        Real.log_neg hdiff.1 hdiff.2
      dsimp [x]
      linarith
    have hlog_lo := Real.log_le_log hcLo hb.1
    rw [Real.log_mul (Real.exp_ne_zero _) hdiff.1.ne', Real.log_exp]
      at hlog_lo
    have hnum : x + Real.log cLo ≤ clock β * logEigen := by
      dsimp [x, logEigen]
      linarith
    have hclock_lower : (x + Real.log cLo) / logEigen ≤ clock β := by
      exact (div_le_iff₀ hlogEigen_pos).2 hnum
    have hclock_lower_div :
        (x + Real.log cLo) / logEigen / x ≤ clock β / x := by
      exact div_le_div_of_nonneg_right hclock_lower hxpos.le
    calc
      (1 + Real.log cLo / (-Real.log (M.betaC - β))) / logEigen =
          (x + Real.log cLo) / logEigen / x := by
        change (1 + Real.log cLo / x) / logEigen =
          (x + Real.log cLo) / logEigen / x
        field_simp [hlogEigen_pos.ne', hxpos.ne']
      _ ≤ clock β / x := hclock_lower_div
      _ = clock β / (-Real.log (M.betaC - β)) := by rfl
  · filter_upwards
      [hannulus,
        Ioo_mem_nhdsLT (show M.betaC - (1 : ℝ) < M.betaC by norm_num)]
      with β hb hβdist
    let x := -Real.log (M.betaC - β)
    have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβdist.1, hβdist.2]
    have hxpos : 0 < x := by
      have hlogneg : Real.log (M.betaC - β) < 0 :=
        Real.log_neg hdiff.1 hdiff.2
      dsimp [x]
      linarith
    have hprod_pos :
        0 < Real.exp (clock β * Real.log relevantEigenvalue) *
            (M.betaC - β) :=
      lt_of_lt_of_le hcLo hb.1
    have hlog_hi := Real.log_le_log hprod_pos hb.2
    rw [Real.log_mul (Real.exp_ne_zero _) hdiff.1.ne', Real.log_exp]
      at hlog_hi
    have hnum : clock β * logEigen ≤ x + Real.log cHi := by
      dsimp [x, logEigen]
      linarith
    have hclock_upper : clock β ≤ (x + Real.log cHi) / logEigen := by
      exact (le_div_iff₀ hlogEigen_pos).2 hnum
    have hclock_upper_div :
        clock β / x ≤ (x + Real.log cHi) / logEigen / x := by
      exact div_le_div_of_nonneg_right hclock_upper hxpos.le
    calc
      clock β / (-Real.log (M.betaC - β)) = clock β / x := by rfl
      _ ≤ (x + Real.log cHi) / logEigen / x := hclock_upper_div
      _ = (1 + Real.log cHi / (-Real.log (M.betaC - β))) / logEigen := by
        change (x + Real.log cHi) / logEigen / x =
          (1 + Real.log cHi / x) / logEigen
        field_simp [hlogEigen_pos.ne', hxpos.ne']

end Exact3D
end StatMech
