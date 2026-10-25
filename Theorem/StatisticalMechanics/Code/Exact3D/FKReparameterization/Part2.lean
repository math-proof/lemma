/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part2


namespace StatMech

namespace Exact3D

namespace FKReparameterization

theorem pOfBetaDistancePrefactor_eq_slope {βc β : ℝ} (hβ : β ≠ βc) :
    pOfBetaDistancePrefactor βc β = slope IsingFK.pOfBeta βc β := by
  unfold pOfBetaDistancePrefactor
  rw [slope_def_field]
  have hden : β - βc ≠ 0 := sub_ne_zero.mpr hβ
  field_simp [hden]
  ring


theorem pOfBetaDistancePrefactor_pos_of_lt {βc β : ℝ} (hβ : β < βc) :
    0 < pOfBetaDistancePrefactor βc β := by
  unfold pOfBetaDistancePrefactor
  exact div_pos (sub_pos.mpr (pOfBeta_strictMono hβ)) (sub_pos.mpr hβ)


theorem pOfBeta_criticalDistance_eq_prefactor_mul
    {βc β : ℝ} (hβ : β ≠ βc) :
    IsingFK.pOfBeta βc - IsingFK.pOfBeta β =
      pOfBetaDistancePrefactor βc β * (βc - β) := by
  unfold pOfBetaDistancePrefactor
  have hden : βc - β ≠ 0 := sub_ne_zero.mpr hβ.symm
  field_simp [hden]


theorem tendsto_pOfBetaDistancePrefactor_left (βc : ℝ) :
    Filter.Tendsto (pOfBetaDistancePrefactor βc)
      (nhdsWithin βc (Set.Iio βc)) (nhds (2 * Real.exp (-2 * βc))) := by
  have hslope :
      Filter.Tendsto (slope IsingFK.pOfBeta βc)
        (nhdsWithin βc (Set.Iio βc)) (nhds (2 * Real.exp (-2 * βc))) := by
    exact (hasDerivAt_pOfBeta βc).tendsto_slope.mono_left
      (nhdsWithin_mono βc (fun β hβ => ne_of_lt hβ))
  refine Filter.Tendsto.congr' ?_ hslope
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact (pOfBetaDistancePrefactor_eq_slope (ne_of_lt hβ)).symm


theorem tendsto_log_pOfBetaDistancePrefactor_div_log_left (βc : ℝ) :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (pOfBetaDistancePrefactor βc β) / Real.log (βc - β))
      (nhdsWithin βc (Set.Iio βc)) (nhds 0) := by
  let a : ℝ := 2 * Real.exp (-2 * βc)
  have ha : 0 < a := by
    positivity
  have hpref :
      Filter.Tendsto (pOfBetaDistancePrefactor βc)
        (nhdsWithin βc (Set.Iio βc)) (nhds a) := by
    simpa [a] using tendsto_pOfBetaDistancePrefactor_left βc
  have hlogpref :
      Filter.Tendsto (fun β : ℝ => Real.log (pOfBetaDistancePrefactor βc β))
        (nhdsWithin βc (Set.Iio βc)) (nhds (Real.log a)) :=
    (Real.continuousAt_log ha.ne').tendsto.comp hpref
  have hlogd :
      Filter.Tendsto (fun β : ℝ => Real.log (βc - β))
        (nhdsWithin βc (Set.Iio βc)) Filter.atBot := by
    simpa [ParameterModel] using
      tendsto_log_betaC_sub_atBot (ParameterModel βc)
  exact hlogpref.div_atBot hlogd

set_option linter.style.longLine false in


theorem eventually_pOfBetaDistancePrefactor_mem_Ioo_left (βc : ℝ) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
      pOfBetaDistancePrefactor βc β ∈
        Set.Ioo (Real.exp (-2 * βc)) (3 * Real.exp (-2 * βc)) := by
  let a : ℝ := 2 * Real.exp (-2 * βc)
  have h_exp_pos : 0 < Real.exp (-2 * βc) := Real.exp_pos _
  have hleft : Real.exp (-2 * βc) < a := by
    dsimp [a]
    linarith
  have hright : a < 3 * Real.exp (-2 * βc) := by
    dsimp [a]
    linarith
  have hmem :
      a ∈ Set.Ioo (Real.exp (-2 * βc)) (3 * Real.exp (-2 * βc)) :=
    ⟨hleft, hright⟩
  have hopen :
      IsOpen (Set.Ioo (Real.exp (-2 * βc)) (3 * Real.exp (-2 * βc))) :=
    isOpen_Ioo
  exact (tendsto_pOfBetaDistancePrefactor_left βc).eventually
    (hopen.mem_nhds hmem)

set_option linter.style.longLine false in


theorem eventually_pOfBeta_criticalDistance_comparable_left (βc : ℝ) :
    ∀ᶠ β in nhdsWithin βc (Set.Iio βc),
      Real.exp (-2 * βc) * (βc - β) ≤
          IsingFK.pOfBeta βc - IsingFK.pOfBeta β ∧
        IsingFK.pOfBeta βc - IsingFK.pOfBeta β ≤
          (3 * Real.exp (-2 * βc)) * (βc - β) := by
  filter_upwards
    [eventually_pOfBetaDistancePrefactor_mem_Ioo_left βc,
      self_mem_nhdsWithin] with β hpref hβ
  have hdist :=
    pOfBeta_criticalDistance_eq_prefactor_mul (βc := βc) (β := β)
      (ne_of_lt hβ)
  have hdiff_nonneg : 0 ≤ βc - β := le_of_lt (sub_pos.mpr hβ)
  constructor
  · rw [hdist]
    exact mul_le_mul_of_nonneg_right (le_of_lt hpref.1) hdiff_nonneg
  · rw [hdist]
    exact mul_le_mul_of_nonneg_right (le_of_lt hpref.2) hdiff_nonneg

set_option linter.style.longLine false in


theorem exists_Ioo_subset_of_eventually_left {βc : ℝ} {P : ℝ → Prop}
    (hP : ∀ᶠ β in nhdsWithin βc (Set.Iio βc), P β) :
    ∃ δ, 0 < δ ∧ ∀ β, β ∈ Set.Ioo (βc - δ) βc → P β := by
  rw [eventually_nhdsWithin_iff] at hP
  rw [Metric.eventually_nhds_iff] at hP
  obtain ⟨ε, hε, hPε⟩ := hP
  refine ⟨ε / 2, by positivity, ?_⟩
  intro β hβ
  have hdist : dist β βc < ε := by
    rw [Real.dist_eq]
    have hle : β - βc ≤ 0 := sub_nonpos.mpr (le_of_lt hβ.2)
    have habs : |β - βc| = βc - β := by
      rw [abs_of_nonpos hle]
      ring
    rw [habs]
    linarith [hβ.1]
  exact hPε hdist hβ.2

set_option linter.style.longLine false in


theorem exists_pOfBeta_criticalDistance_comparable_Ioo_left (βc : ℝ) :
    ∃ δ, 0 < δ ∧
      ∀ β, β ∈ Set.Ioo (βc - δ) βc →
        Real.exp (-2 * βc) * (βc - β) ≤
            IsingFK.pOfBeta βc - IsingFK.pOfBeta β ∧
          IsingFK.pOfBeta βc - IsingFK.pOfBeta β ≤
            (3 * Real.exp (-2 * βc)) * (βc - β) :=
  exists_Ioo_subset_of_eventually_left
    (eventually_pOfBeta_criticalDistance_comparable_left βc)

end FKReparameterization
end Exact3D
end StatMech
