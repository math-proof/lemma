/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionReduction.Part2
open Set Filter Topology


namespace StatMech.Ising

theorem surfaceTension_pos_iff_ordered_of_weak_bounds
    (J betaC : ℝ) (M tau : ℝ → ℝ)
    (hJ : 0 < J)
    (hregime : HasOrderedMagnetizationRegime M betaC)
    (htauNonneg : ∀ beta, 0 ≤ beta → 0 ≤ tau beta)
    (hupper : ∀ beta, 0 ≤ beta →
      tau beta ≤ 2 * J * beta * (M beta) ^ 2)
    (hweak : HasWeakSurfaceTensionLowerBound J M tau) :
    ∀ beta, 0 ≤ beta → (0 < tau beta ↔ betaC < beta) := by
  intro beta hbeta
  constructor
  · intro htau
    by_contra hnot
    have hle : beta ≤ betaC := not_lt.mp hnot
    have hMzero := hregime.2.1 beta hbeta hle
    have hup := hupper beta hbeta
    rw [hMzero] at hup
    norm_num at hup
    exact (not_lt_of_ge hup) htau
  · intro hcb
    let a := (betaC + beta) / 2
    have hca : betaC < a := by dsimp [a]; linarith
    have hab : a < beta := by dsimp [a]; linarith
    have ha0 : 0 < a := hregime.1.trans hca
    have hMa : 0 < M a := hregime.2.2 a hca
    have hinc := hweak a beta ha0 hab.le
    have hpositive : 0 < 2 * J * (M a) ^ 2 * (beta - a) := by positivity
    have htauA : 0 ≤ tau a := htauNonneg a ha0.le
    linarith


theorem surfaceTension_pos_iff_ordered_of_deriv
    (J betaC : ℝ) (M tau : ℝ → ℝ)
    (hJ : 0 < J)
    (hregime : HasOrderedMagnetizationRegime M betaC)
    (hMnonneg : ∀ beta, 0 < beta → 0 ≤ M beta)
    (hMmono : MonotoneOn M (Ioi 0))
    (htauNonneg : ∀ beta, 0 ≤ beta → 0 ≤ tau beta)
    (htauCont : ContinuousOn tau (Ici 0))
    (htauDiff : DifferentiableOn ℝ tau (Ioi 0))
    (hupper : ∀ beta, 0 ≤ beta →
      tau beta ≤ 2 * J * beta * (M beta) ^ 2)
    (hderiv : ∀ beta, 0 < beta →
      2 * J * (M beta) ^ 2 ≤ deriv tau beta) :
    ∀ beta, 0 ≤ beta → (0 < tau beta ↔ betaC < beta) := by
  apply surfaceTension_pos_iff_ordered_of_weak_bounds
    J betaC M tau hJ hregime htauNonneg hupper
  exact weakSurfaceTensionLowerBound_of_deriv J M tau hJ.le
    hMnonneg hMmono htauCont htauDiff hderiv


theorem isingSurfaceTension_pos_iff_ordered_reduction
    (d : ℕ) (J betaC : ℝ) (tau : ℝ → ℝ)
    (hJ : 0 < J)
    (hregime : HasOrderedMagnetizationRegime (magnetization d) betaC)
    (hMnonneg : ∀ beta, 0 < beta → 0 ≤ magnetization d beta)
    (hMmono : MonotoneOn (magnetization d) (Ioi 0))
    (htauNonneg : ∀ beta, 0 ≤ beta → 0 ≤ tau beta)
    (htauCont : ContinuousOn tau (Ici 0))
    (htauDiff : DifferentiableOn ℝ tau (Ioi 0))
    (hupper : ∀ beta, 0 ≤ beta →
      tau beta ≤ 2 * J * beta * (magnetization d beta) ^ 2)
    (hderiv : ∀ beta, 0 < beta →
      2 * J * (magnetization d beta) ^ 2 ≤ deriv tau beta) :
    ∀ beta, 0 ≤ beta → (0 < tau beta ↔ betaC < beta) :=
  surfaceTension_pos_iff_ordered_of_deriv J betaC (magnetization d) tau
    hJ hregime hMnonneg hMmono htauNonneg htauCont htauDiff hupper hderiv

end StatMech.Ising
