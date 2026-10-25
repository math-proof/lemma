/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformArcosh
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductReduction
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingScalarNormalizationLimit
import Theorem.StatisticalMechanics.Code.Onsager.RiemannPeriodicMidpoint
import Mathlib.Analysis.Calculus.MeanValue
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part3
open Filter Set
open scoped Topology BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

theorem quantumIsingShiftedTrotterModeContribution_tendstoUniformly
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    TendstoUniformly (quantumIsingShiftedTrotterModeContribution beta h)
      (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) atTop := by
  have hrapid := quantumIsingScaledArcosh_tendstoUniformly_dispersion
    beta h hbeta hh
  have hcorr := quantumIsingRapidityCorrection_lipschitz.uniformContinuous
    |>.comp_tendstoUniformly hrapid
  have hnorm := (quantumIsingModeScalarNormalization_tendsto_zero
    beta h hbeta hh).tendstoUniformly_const (α := Real)
  have hsum := hnorm.add hcorr
  convert hsum using 1
  · funext k
    rw [Pi.add_apply, zero_add, Function.comp_apply,
      quantumIsingRapidityCorrection_eq_cosh]
    unfold quantumIsingModeLog
    congr 3
    ring

end StatMech.FrontierA
