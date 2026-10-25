/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part12


namespace StatMech.Onsager

theorem ons_pressureComplex_differentiableOn_noncritical {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    DifferentiableOn ℂ ons_pressureComplex
      (ons_complexNoncriticalNeighborhood beta) := by
  intro z hz
  have hdouble := ons_hasDerivAt_complexDoubleIntegral_noncritical hbeta hcrit hz
  unfold ons_pressureComplex ons_freeEnergyIntegralComplex
  exact ((hasDerivAt_const z (Real.log 2 : ℂ)).add
    (hdouble.const_mul (1 / (8 * Real.pi ^ 2) : ℂ))).differentiableAt.differentiableWithinAt

theorem ons_pressureComplex_analyticAt_noncritical {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    AnalyticAt ℂ ons_pressureComplex (beta : ℂ) := by
  exact (ons_pressureComplex_differentiableOn_noncritical hbeta hcrit).analyticAt
    (ons_complexNoncriticalNeighborhood_mem_nhds hbeta hcrit)

theorem ons_complexLogGInt_ofReal {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) (k1 k2 : ℝ) :
    Complex.log (ons_gIntComplex (beta : ℂ) k1 k2) =
      (Real.log (ons_gInt beta k1 k2) : ℂ) := by
  rw [ons_gIntComplex_ofReal]
  exact (Complex.ofReal_log
    (le_trans (sq_nonneg _) (ons_gInt_lower_noncritical_base hbeta hcrit))).symm

theorem ons_complexDoubleIntegral_ofReal {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    (∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Complex.log (ons_gIntComplex (beta : ℂ) k1 k2)) =
      Complex.ofReal (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (ons_gInt beta k1 k2)) := by
  calc
    (∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Complex.log (ons_gIntComplex (beta : ℂ) k1 k2)) =
        ∫ k1 in (-Real.pi)..Real.pi,
          Complex.ofReal (∫ k2 in (-Real.pi)..Real.pi,
            Real.log (ons_gInt beta k1 k2)) := by
              apply intervalIntegral.integral_congr
              intro k1 _hk1
              calc
                (∫ k2 in (-Real.pi)..Real.pi,
                  Complex.log (ons_gIntComplex (beta : ℂ) k1 k2)) =
                    ∫ k2 in (-Real.pi)..Real.pi,
                      (Real.log (ons_gInt beta k1 k2) : ℂ) := by
                        apply intervalIntegral.integral_congr
                        intro k2 _hk2
                        exact ons_complexLogGInt_ofReal hbeta hcrit k1 k2
                _ = Complex.ofReal (∫ k2 in (-Real.pi)..Real.pi,
                    Real.log (ons_gInt beta k1 k2)) :=
                  intervalIntegral.integral_ofReal
    _ = Complex.ofReal (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (ons_gInt beta k1 k2)) :=
      intervalIntegral.integral_ofReal

theorem ons_pressureComplex_ofReal {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    ons_pressureComplex (beta : ℂ) = (ons_pressure beta : ℂ) := by
  unfold ons_pressureComplex ons_freeEnergyIntegralComplex
  rw [ons_complexDoubleIntegral_ofReal hbeta hcrit]
  unfold ons_pressure ons_freeEnergyIntegral
  push_cast
  rfl


theorem ons_pressure_analyticAt_noncritical {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    AnalyticAt ℝ ons_pressure beta := by
  have hc := (ons_pressureComplex_analyticAt_noncritical hbeta hcrit).re_ofReal
  apply hc.congr
  filter_upwards [ons_noncriticalNeighborhood_mem_nhds hbeta hcrit] with b hb
  rw [ons_pressureComplex_ofReal hb.1
    (ons_noncriticalNeighborhood_ne_betaC hbeta hcrit hb)]
  simp


theorem ons_phase_regularity :
    (∀ beta : ℝ, 0 < beta → beta ≠ ons_betaC →
      AnalyticAt ℝ ons_pressure beta) ∧
    ContDiffAt ℝ 1 ons_pressure ons_betaC ∧
    HasDerivAt ons_pressure (Real.sqrt 2) ons_betaC ∧
    (∀ n : ℕ, -4 + (32 / 5 : ℝ) * (n : ℝ) ≤
      ∫ x in Real.exp (-(n : ℝ))..1,
        ∫ y in x..(2 * x),
          ons_logGIntBetaDeriv2 ons_betaC x y) ∧
    Filter.Tendsto
      (fun n : ℕ =>
        (∫ x in (-Real.pi)..(-Real.exp (-(n : ℝ))),
            ∫ y in (-Real.pi)..Real.pi,
              ons_logGIntBetaDeriv2 ons_betaC x y) +
          ∫ x in Real.exp (-(n : ℝ))..Real.pi,
            ∫ y in (-Real.pi)..Real.pi,
              ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  exact ⟨fun beta hbeta hcrit =>
      ons_pressure_analyticAt_noncritical hbeta hcrit,
    ons_pressure_contDiffAt_one_betaC,
    ons_hasDerivAt_pressure_betaC,
    ons_criticalSecond_wedgeCutoff_lower,
    ons_criticalSecond_fullCutoff_tendsto⟩

end StatMech.Onsager
